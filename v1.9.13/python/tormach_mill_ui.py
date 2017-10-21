#!/usr/bin/env python

#import pygtk
#pygtk.require("2.0")

# for debugging within Wing IDE
try:
    import wingdbstub
except ImportError:
    pass

import gtk
import glib
import gobject
import sys
import redis
import linuxcnc
import hal
import gremlin
import os
import pango
import subprocess
import math
import errno
import time
import csv
import re
import threading
import logging
from ui_common import *


try:
    from fontTools import ttLib
    is_ttlib = True
except:
    is_ttlib = False

# Tormach modules
from constants import *
from errors import *
import mill_conversational
import probing
import numpad
import tormach_file_util
import zbot_atc
from ui_common import *

try:
    import scanner2
    _scanner_available = True
except ImportError as err:
    logging.warn("Scanner module not available due to missing modules:\n\t{0}".format(err))
    _scanner_available = False


logging.basicConfig(level=logging.DEBUG, format='(%(threadName)-10s) %(message)s')


#FIXME: Redefined from constants page
MAIN_PAGE = 0
FILE_PAGE = 1
SETTINGS_PAGE = 2
OFFSETS_PAGE = 3
CONVERSATIONAL_PAGE = 4
PROBE_PAGE = 5
ATC_PAGE = 6
CNC_SCANNER_PAGE = 7
INJECTOR_PAGE = 8
MILL_STATUS_PAGE = 9
DRILL_TABLE_BASIC_SIZE = 100

TOOL_TABLE_ROWS = 255
JOB_TABLE_ROWS = 30

class AxisState:
    """Simple class to store GUI axis data in iterable types with a numerical index."""
    def __init__(self):
        self.letters = ['x','y','z','a']
        self.dros = ['%s_dro' % l for l in self.letters]
        self.dtg_labels = ['%s_dtg_label' % l for l in self.letters]
        self.referenced = [False for l in self.letters]
        self.at_limit_display = [False for l in self.letters]
        #KLUDGE: skipping A axis home switch the easy way until hal pins are added
        self.home_switches=['home-switch-%s' % l for l in self.letters[0:3]]
        self.limit_leds=['%s_limit_led' % l for l in self.letters]
        self.ref_buttons = ['ref_%s' % l for l in self.letters]
        self.jog_enabled_local = [False for l in self.letters]
        self.jog_active_leds=['jog_%s_active_led' % l for l in self.letters]



class mill(TormachUIBase):

    def __init__(self):
        # redis db for persistent storage.  File location set in redis.conf, currently in config dir (rdb.dump)
        self.redis = redis.Redis()

        # glade setup
        gladefile = os.path.join(GLADE_DIR, 'tormach_mill_ui.glade')
        self.builder = gtk.Builder()
        #Add a shortcut to the get_object function here
        self.get_obj = self.builder.get_object
        self.builder.add_from_file(gladefile)

        # Setup the builder above so that the base UI class can use it as needed
        TormachUIBase.__init__(self)

        self.machine_type = MACHINE_TYPE_MILL
        self.program_exit_code = EXITCODE_SHUTDOWN
        self.DRILL_LIST_BASIC_SIZE =int(DRILL_TABLE_BASIC_SIZE)
        self.DRILL_TABLE_ROWS = int(DRILL_TABLE_BASIC_SIZE)

        #####################################################################
        # Initialization steps that don't depend on GTK

        # Define sets of keys that are disabled depending on the current page
        self.setup_key_sets()

        self.builder.connect_signals(self)

        # retrieve main window, notebooks, fixed containers
        self.window = self.builder.get_object("main_window")
        self.notebook = self.builder.get_object("notebook")
        self.probe_notebook = self.builder.get_object("probe_notebook")

        self.conv_notebook = self.builder.get_object("conversational_notebook")
        self.offsets_notebook = self.builder.get_object("offsets_notebook")
        self.fixed = self.builder.get_object("fixed")
        self.notebook_main_fixed = self.builder.get_object("notebook_main_fixed")
        self.notebook_file_util_fixed = self.builder.get_object("notebook_file_util_fixed")
        self.tool_offsets_fixed = self.builder.get_object("tool_offsets_fixed")
        self.work_offsets_fixed = self.builder.get_object("work_offsets_fixed")
        self.conv_drill_tap_pattern_notebook_fixed = self.builder.get_object("conv_drill_tap_pattern_notebook_fixed")
        self.conv_drill_tap_pattern_notebook = self.builder.get_object("conv_drill_tap_pattern_notebook_type")
        self.atc_fixed = self.builder.get_object("atc_fixed")
        self.conv_job_fixed      = self.builder.get_object('conv_job_fixed')
        self.conv_engrave_fixed  = self.builder.get_object("conv_engrave_fixed")
        self.camera_notebook     = self.builder.get_object("camera_notebook")
        self.preview_image_overlay = self.builder.get_object("preview_image_overlay")

        # throw out mousewheel events to prevent scrolling through notebooks on wheel
        self.notebook.connect("scroll-event", self.on_mouse_wheel_event)
        self.conv_notebook.connect("scroll-event", self.on_mouse_wheel_event)
        self.offsets_notebook.connect("scroll-event", self.on_mouse_wheel_event)

        self.last_gcode_program_path = ''  #save this after loading program
        # --------------------------------------------------------
        # linuxcnc command and status objects
        # --------------------------------------------------------
        self.command = linuxcnc.command()
        self.status = linuxcnc.stat()
        self.error = linuxcnc.error_channel()

        # --------------------------------------------------------
        # gremlin tool path display setup
        # --------------------------------------------------------
        ini_file_name = sys.argv[2]
        inifile = linuxcnc.ini(ini_file_name)
        self.inifile = inifile
        self.gremlin = Tormach_Mill_Gremlin(self,680,410)
        self.notebook_main_fixed.put(self.gremlin, 322, 0)

        self.notebook_main_fixed.put(self.message_line, 322, 372)
        self.clear_message_line_text()

        self.notify_at_cycle_start = False  # when message text superimposed in Gremlin
        self.notify_answer_key = ''
        self.only_one_cable_warning = False  # warn when false

        # elapsed time label on top of gremlin
        # the Gtk fixed container doesn't support control over z-order of overlapping widgets.
        # so the behavior we get is arbitrary and seems to depend on order of adding the
        # widget to the container.  sweet.
        self.notebook_main_fixed.put(self.elapsed_time_label, 935, 388)

        # max feedrate for user entry validation (in machine setup units - ipm)
        self.max_feedrate = 60 * self.ini_float('AXIS_0', 'MAX_VELOCITY', 135)

        # trajmaxvel from ini for maxvel slider
        self.maxvel_lin = self.ini_float('TRAJ', 'MAX_VELOCITY', 3)
        self.maxvel_ang = self.ini_float('TRAJ', 'MAX_ANGULAR_VELOCITY', 22)



        # -------------------------------------------------------------
        # HAL setup.  Pins/signals must be connected in POSTGUI halfile
        # -------------------------------------------------------------

        self.hal = hal.component("tormach")

        self.hal.newpin("config",hal.HAL_S32,hal.HAL_OUT)  # let the world know who we are

        self.hal.newpin("coolant", hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin("coolant-iocontrol", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("mist", hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin("mist-iocontrol", hal.HAL_BIT, hal.HAL_IN)

        self.hal.newpin("jog-axis-x-enabled", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("jog-axis-y-enabled", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("jog-axis-z-enabled", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("jog-axis-a-enabled", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("jog-step-button", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("jog-counts", hal.HAL_S32, hal.HAL_IN)
        self.hal.newpin("jog-ring-speed-signed", hal.HAL_FLOAT, hal.HAL_IN)
        self.hal.newpin("jog-ring-selected-axis", hal.HAL_S32, hal.HAL_IN)
        self.hal.newpin("jog-gui-step-index", hal.HAL_U32, hal.HAL_OUT)
        self.hal.newpin("jog-is-metric", hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin("jog-ring-speed-1", hal.HAL_FLOAT, hal.HAL_OUT)
        self.hal.newpin("jog-ring-speed-2", hal.HAL_FLOAT, hal.HAL_OUT)
        self.hal.newpin("jog-ring-speed-3", hal.HAL_FLOAT, hal.HAL_OUT)
        self.hal.newpin("jog-ring-speed-4", hal.HAL_FLOAT, hal.HAL_OUT)
        self.hal.newpin("jog-ring-speed-5", hal.HAL_FLOAT, hal.HAL_OUT)
        self.hal.newpin("jog-ring-speed-6", hal.HAL_FLOAT, hal.HAL_OUT)
        self.hal.newpin("jog-ring-speed-7", hal.HAL_FLOAT, hal.HAL_OUT)

        self.hal.newpin("motion-program-line", hal.HAL_S32, hal.HAL_IN)
        self.hal.newpin("motion-next-program-line", hal.HAL_S32, hal.HAL_IN)
        self.hal.newpin("motion-completed-program-line", hal.HAL_S32, hal.HAL_IN)

        self.hal.newpin("spindle-range", hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin("spindle-range-alarm", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("spindle-type", hal.HAL_S32, hal.HAL_OUT)
        self.hal.newpin("spindle-hispeed-min", hal.HAL_FLOAT, hal.HAL_OUT)
        self.hal.newpin("spindle-hispeed-max", hal.HAL_FLOAT, hal.HAL_OUT)
        self.hal.newpin("spindle-min-speed", hal.HAL_FLOAT, hal.HAL_IN)
        self.hal.newpin("spindle-max-speed", hal.HAL_FLOAT, hal.HAL_IN)
        self.hal.newpin("spindle-disable", hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin("spindle-on", hal.HAL_BIT, hal.HAL_IN)

        # enclosure door switch
        self.hal.newpin("enc-door-switch-status", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("enc-door-switch-configured", hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin("enc-door-open-max-rpm", hal.HAL_FLOAT, hal.HAL_OUT)

        # height gauge
        self.hal.newpin('hg-height', hal.HAL_FLOAT, hal.HAL_IN)
        self.hal.newpin('hg-zero-offset', hal.HAL_FLOAT, hal.HAL_IN)
        self.hal.newpin('hg-button-changed', hal.HAL_BIT, hal.HAL_IO)
        self.hal.newpin('hg-button-pressed', hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin('hg-mm-mode', hal.HAL_BIT, hal.HAL_IO)
        self.hal.newpin('hg-set-zero-offset', hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin('hg-present', hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin('hg-debug', hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin('hg-enable', hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin('hg-has-zero-button', hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("probe-active-high", hal.HAL_BIT, hal.HAL_OUT)
        self.zero_height_gauge_visible = True


        self.hal.newpin("mesa-watchdog-has-bit", hal.HAL_BIT, hal.HAL_IO)
        self.hal.newpin("cycle-time-hours", hal.HAL_U32, hal.HAL_IN)
        self.hal.newpin("cycle-time-minutes", hal.HAL_U32, hal.HAL_IN)
        self.hal.newpin("cycle-time-seconds", hal.HAL_U32, hal.HAL_IN)

        # commanded speed feedback for Spindle DROs during g code program exectuion
        self.hal.newpin("spindle-speed-out", hal.HAL_FLOAT, hal.HAL_IN)
        self.hal.newpin("machine-ok", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("home-switch-x", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("home-switch-y", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("home-switch-z", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("home-switch-enable", hal.HAL_BIT, hal.HAL_OUT)

        #atc pins
        self.hal.newpin("atc-hal-request", hal.HAL_FLOAT, hal.HAL_OUT)
        self.hal.newpin("atc-hal-data", hal.HAL_FLOAT, hal.HAL_OUT)
        self.hal.newpin("atc-hal-return", hal.HAL_FLOAT, hal.HAL_IN)
        self.hal.newpin("atc-hal-busy",hal.HAL_BIT,hal.HAL_IN)
        self.hal.newpin("atc-device-status", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("atc-pressure-status", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("atc-tray-status", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("atc-vfd-status", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("atc-draw-status", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("atc-tray-position", hal.HAL_FLOAT, hal.HAL_IN)
        self.hal.newpin("atc-ngc-running", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("atc-tools-in-tray",hal.HAL_U32,hal.HAL_IN)

        # usbio board pins for board one
        self.hal.newpin("usbio-enabled", hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin("usbio-input-0", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("usbio-input-1", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("usbio-input-2", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("usbio-input-3", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("usbio-output-0", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("usbio-output-1", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("usbio-output-2", hal.HAL_BIT, hal.HAL_IN)
        self.hal.newpin("usbio-output-3", hal.HAL_BIT, hal.HAL_IN)

        # usbio status for all boards as a group
        self.hal.newpin("usbio-status",hal.HAL_S32, hal.HAL_IN)

        #manual control of smart_cool nozzle - hot key connected
        self.hal.newpin("smart-cool-man-auto", hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin("smart-cool-up", hal.HAL_BIT, hal.HAL_OUT)
        self.hal.newpin("smart-cool-down", hal.HAL_BIT, hal.HAL_OUT)


        # prompting communication - all responses to Gremlin messages or NGC prompts set this pin
        #   used by ATC
        self.hal.newpin("prompt-reply", hal.HAL_FLOAT, hal.HAL_OUT)

        self.hal.ready()


        # errors
        self.error_handler = error_handler(self.builder, self.moving, self.hal)



        # g code file history combo box
        self.file_history_liststore = gtk.ListStore(str, str)
        self.loaded_gcode_filename_combobox = self.builder.get_object("loaded_gcode_combobox")
        self.loaded_gcode_filename_combobox.set_model(self.file_history_liststore)
        cell = gtk.CellRendererText()
        self.loaded_gcode_filename_combobox.pack_start(cell, True)
        self.loaded_gcode_filename_combobox.add_attribute(cell, 'text', 0)
        try:
            for i in range(0, self.redis.llen('recent_file_history')):
                # file history liststore is in form of ['filename', 'path'], but redis only stores the path
                path = self.redis.lpop('recent_file_history')
                self.file_history_liststore.append([os.path.basename(path), path])
        except:
            self.error_handler.write("Retrieval of recent file history failed.", ALARM_LEVEL_DEBUG)
            pass

        self.file_history_liststore.append([CLEAR_CURRENT_PROGRAM, CLEAR_CURRENT_PROGRAM])

        # --------------------------------------------------------
        # conversational
        # --------------------------------------------------------
        # spindle max/min are used by conversational DROs for validation
        # and the main UI DRO
        # spindle info can change at runtime as 'speeder' or 'hispeed' is selected
        # so do not rely on ranges being static in conversational checks
        # use the provided HAL min/max speeds that the spindle component maintains
        # based upon spindle type and current belt position
        #
        self.conversational = mill_conversational.conversational(self,
                                                                 self.status,
                                                                 self.error_handler,
                                                                 self.redis,
                                                                 self.hal)

        # start with the coolant and mist off
        self.prev_coolant_iocontrol = self.prev_mist_iocontrol = self.hal['coolant'] = self.hal['mist'] = 0
        self.coolant_status = self.mist_status = 0
        self.coolant_ticker = self.mist_ticker = 0
        self.coolant_apply_at = self.mist_apply_at = 0
        self.hardkill_coolant = False   # RESET/STOP kills coolant hard

        #smart cool manual override state -
        self.smart_overriding = False



        # shuttlexpress step button flag
        self.jog_step_button_was_pressed = 0
        self.prev_hal_jog_counts = self.hal['jog-counts']


        # -------------------------------------------------------
        # PostGUI HAL
        # -------------------------------------------------------
        postgui_halfile = inifile.find("HAL", "POSTGUI_HALFILE")
        if postgui_halfile:
            if subprocess.call(["halcmd", "-i", sys.argv[2], "-f", postgui_halfile]):
                print "Error: something failed running halcmd on '" + postgui_halfile + "'"
                sys.exit(1)
        else:
            # complain about missing POSTGUI_HALFILE
            print "Error: missing POSTGUI_HALFILE in .INI file."
            sys.exit(1)

        # configure the ShuttleXpress (if preset)
        postgui_shuttlexpress_halfile = inifile.find("HAL", "POSTGUI_SHUTTLEXPRESS_HALFILE")
        if postgui_shuttlexpress_halfile:
            if subprocess.call(["halcmd", "-i", sys.argv[2], "-f", postgui_shuttlexpress_halfile]):
                print "Warning: something failed running halcmd on '" + postgui_shuttlexpress_halfile + "'"
        else:
            # complain about missing POSTGUI_SHUTTLEXPRESS_HALFILE
            print "Warning: missing POSTGUI_SHUTTLEXPRESS_HALFILE in .INI file."

        # can't set any of these until after postguihal when pins are connected
        self.hal['hg-debug'] = 0
        self.hal['hg-mm-mode'] = 0

        # set door switch configuration off until redis is checked
        self.hal['enc-door-switch-configured'] = 0
        self.hal['enc-door-open-max-rpm']= 1000

        # initialize mesa watchdog status
        self.mesa_watchdog_has_bit_seen = False

        # --------------------------------------------------------
        # config label - 1100 series 1,2,3, 770s, 440
        # --------------------------------------------------------

        config_label = self.builder.get_object('config_label')
        config_label.modify_font(pango.FontDescription('Bebas ultra-condensed 8'))

        config = ini_file_name

        self.is_sim_config = False
        if "sim" in config:
            self.is_sim_config = True

        if "1100-1" in config:
            config = "1100-I"
            self.hal["config"] = CONFIG_1100_1
        elif "1100-2" in config:
            config = "1100-II"
            self.hal["config"] = CONFIG_1100_2
        elif "1100-3" in config:
            config = "1100-3"
            self.hal["config"] = CONFIG_1100_3
        elif "770" in config:
            config = "770"
            self.hal["config"] = CONFIG_770
        elif "440" in config:
            config = "440"
            self.hal["config"] = CONFIG_440
        else:
            config = "Frank"
            self.is_sim_config = True
            probe_button = gtk.Button("Probe - lo ")
            probe_button.connect("button_press_event", self.on_probe_sim_button_press)
            #self.fixed.put(probe_button, 925, 680)
            #probe_button.set_size_request(80, 30)

        if self.is_sim_config:
            self.hal["config"] = CONFIG_SIM
            config += " SIM"

        config_label.set_text(config)
        self.config = config

        # ---------------------------------------------
        # member variable init
        # ---------------------------------------------

        # Set initial toggle button states
        self.axes = AxisState()

        self.status.poll()
        self.g21 = self.prev_g21 = False
        self.ttable_conv = 1.0
        self.jog_metric_scalar = 1
        self.first_run = True
        self.estop_alarm = True
        self.display_estop_msg = False
        self.interp_alarm = False
        self.single_block_active = False
        self.feedhold_active = threading.Event()
        self.m01_break_active = self.status.optional_stop
        self.spindle_direction = self.prev_spindle_direction = self.status.spindle_direction
        self.x_referenced = self.prev_x_referenced = 0
        self.y_referenced = self.prev_y_referenced = 0
        self.z_referenced = self.prev_z_referenced = 0
        self.a_referenced = self.prev_a_referenced = 0
        self.s_word = 0
        self.machine_ok_display = False
        self.door_sw_status = self.prev_door_sw_status = False
        self.program_paused_for_door_sw_open = False
        self.probe_tripped_display = False
        self.notebook_locked = False
        self.cycle_start_led_color = 'dark'
        self.combobox_masked = False
        self.dros_locked = False
        self.jog_ring_axis = self.prev_jog_ring_axis = -1
        self.jogging_stopped = False
        self.key_release_count = 0
        self.reset_image_color = 'red'
        self.is_gcode_program_loaded = False
        self.current_notebook_page = self.prev_notebook_page = MAIN_PAGE
        self.F1_page_toggled = False
        self.tlo_mismatch_count = 0    # track sucessive TLO misalignment
        self.cpu_usage = 0
        self.engrave_just = 'left'
        self.thread_mill_rhlh = 'right'
        self.tool_liststore_stale = 0
        self.current_g5x_offset = self.status.g5x_offset
        self.current_g92_offset= self.status.g92_offset


        #timers for various ATC cabling or connection faults...
        self.atc_hardware_check_count = 0    # ATC comm USB failure timer
        self.atc_cable_check_count = 0       # cable failure timer
        self.usbio_e_message = True         #don't pollute the log  with extra messages


        # editor is called from a wrapper script
        # this script changes the directory to ~/gcode
        # then runs the editor with an LD_PRELOAD
        # for a custom libgtk with locked down file chooser dialog
        # and execs the editor (gedit)
        self.gcode_edit_program_to_run = "editscript"

        self.conv_face_spiral_rect = 'spiral'
        self.conv_thread_mill_ext_int = 'external'
        self.conv_drill_tap = 'drill'
        self.conv_pocket_rect_circ = 'rect'
        self.conv_profile_rect_circ = 'rect'
        self.conv_engrave_flat_circ = 'flat'

        self.scope_circle_dia = 30
        self.scope_row = 0

        self.tap_2x_enabled = False

        # -------------------------------------------------
        # Buttons (gtk.eventbox)
        # -------------------------------------------------

        # create a list of image object names
        self.pixbuf_dict = {}
        #TODO move scanner images to scanner_gui_init
        image_set = ('cycle_start_image', 'single_block_image', 'm01_break_image', 'feedhold_image',
                           'coolant_image', 'ccw_image', 'cw_image', 'spindle_range_image', 'spindle_override_100_image',
                           'feed_override_100_image', 'maxvel_override_100_image', 'reset_image', 'jog_inc_cont_image',
                           'ref_x_image', 'ref_y_image', 'ref_z_image', 'ref_a_image',
                           'jog_0001_image', 'jog_0010_image', 'jog_0100_image', 'jog_1000_image',
                           'jog_x_active_led', 'jog_y_active_led', 'jog_z_active_led', 'jog_a_active_led',
                           'm6_g43_image',
                           'tool_touch_chuck', 'touch_z_image',
                           'set_g30_image', 'x_limit_led', 'y_limit_led', 'z_limit_led',
                           'touch_entire_tray_ets_image', 'acc_input_led', 'acc_input_led1', 'acc_input_led2', 'acc_input_led3',
                           'probe_sensor_set_image', 'ets_image',
                           'injection_molder_image', 'door_sw_led', 'machine_ok_led',
                           'usbio_input_0_led', 'usbio_input_1_led', 'usbio_input_2_led', 'usbio_input_3_led',
                           'usbio_output_0_led', 'usbio_output_1_led', 'usbio_output_2_led', 'usbio_output_3_led',
                           'face_spiral_rect_btn_image',
                           'thread_mill_ext_int_btn_image',
                           'drill_tap_btn_image',
                           'drill_tap_detail_image', 'drill_tap_main_image',
                           'drill_tap_clear_table_btn_image',
                           'drill_tap_raise_in_table_btn_image', 'drill_tap_lower_in_table_btn_image',
                           'conv_face_main_image',
                           'pocket_rect_circ_btn_image', 'profile_rect_circ_btn_image', 'conv_pocket_main_image', 'conv_profile_main_image', 'thread_mill_main_image',
                           'thread_mill_detail_image',
                           'atc_remove_image', 'atc_insert_image', 'atc_drawbar_image', 'atc_blast_image', 'set_tool_change_z_image', 'atc_tray_image',
                           'tray_in_led', 'vfd_running_led', 'pressure_sensor_led',
                           'scanner_camera_on_off_image', 'scanner_camera_snap_image',
                           'scanner_status_update_image', 'scanner_scan_start_image',
                           'scanner_calibration_set_p1_image', 'scanner_calibration_set_p2_image',
                           'scanner_calibration_zoom_p1_image', 'scanner_calibration_zoom_p2_image',
                           'scanner_scope_capture_image', 'cam_post_to_file_image', 'finish-editing-button', 'expandview_button_image')

        # create dictionary of key value pairs of image names, image objects
        self.image_list = dict(((i, self.builder.get_object(i))) for i in image_set)

        # gtk.eventboxes
        self.button_list = ('cycle_start', 'single_block', 'm01_break', 'feedhold', 'stop', 'coolant', 'reset',
                            'feedrate_override', 'rpm_override', 'maxvel_override', 'jog_inc_cont',
                            'ref_x', 'ref_y', 'ref_z', 'ref_a',
                            'zero_x', 'zero_y', 'zero_z', 'zero_a',
                            'jog_0001', 'jog_0010', 'jog_0100', 'jog_1000',
                            'ccw', 'spindle_stop', 'cw', 'spindle_range', 'm6_g43',
                            'set_g30', 'goto_g30', 'touch_z', 'atc_fwd',
                            'exit',
                            'switch_to_lathe',
                            'atc_insert', 'atc_delete', 'atc_delete_all', 'atc_tray_forward', 'atc_tray_reverse',
                            'atc_goto_tray_load', 'atc_retract', 'atc_drawbar', 'atc_blast', 'atc_ref_tray',
                            'atc_minus_minus', 'atc_plus_plus', 'atc_remove', 'atc_rev', 'atc_fw',
                            'atc_store', 'atc_touch_entire_tray', 'atc_set_tool_change_z',
                            'inject',
                            'post_to_file', 'append_to_file', 'update', 'exit', 'clear', 'zero_height_gauge',
                            'probe_find_corner',
                            'probe_x_plus', 'probe_x_minus',
                            'probe_y_plus', 'probe_y_minus',
                            'probe_z_minus', 'move_and_set_work_offset',
                            'probe_y_plus_a', 'probe_y_plus_b', 'probe_y_plus_c',
                            'probe_find_rect_boss_center', 'probe_find_circ_boss_center',
                            'probe_find_pocket_center', 'probe_find_pocket_x_center', 'probe_find_pocket_y_center',
                            'probe_set_probe_length', 'probe_a_axis_center',
                            #'probe_set_work_offset',
                            'move_and_set_tool_length',
                            'probe_set_gauge_ref',
                            'face_spiral_rect',
                            'thread_mill_ext_int',
                            'drill_tap', 'drill_tap_clear_table',
                            'drill_tap_lower_in_table', 'drill_tap_raise_in_table',
                            'drill_tap_insert_row_table','drill_tap_delete_row_table',
                            'profile_rect_circ',
                            'pocket_rect_circ',
                            'probe_origin_x_plus', 'probe_origin_x_minus',
                            'probe_origin_y_plus', 'probe_origin_y_minus',
                            'probe_origin_z_minus',
                            'scanner_camera_on_off', 'scanner_camera_snap',
                            'scanner_status_update', 'scanner_scan_start',
                            'scanner_calibration_set_p1', 'scanner_calibration_set_p2',
                            'scanner_calibration_zoom_p1', 'scanner_calibration_zoom_p2',
                            'scanner_scope_capture', 'cam_post_to_file','expandview_button',
                            'usbio_output_0_led_button', 'usbio_output_1_led_button', 'usbio_output_2_led_button', 'usbio_output_3_led_button' )

        # create dictionary of glade names, eventbox objects
        self.button_list = dict(((i, self.builder.get_object(i))) for i in self.button_list)

        # Create additional buttons manually
        self.setup_gcode_buttons()
        self.setup_copy_buttons()

        # get initial x/y locations for eventboxes
        for name, eventbox in self.button_list.iteritems():
            eventbox.x = get_x_pos(eventbox)
            eventbox.y = get_y_pos(eventbox)
            # add permissions flag to each button - default is only can use when the machine is out of estop and at rest
            eventbox.permission_level = PERMISSION_OK_WHEN_IDLE

        self.set_button_permissions()



        # ------------------------------------------------
        # DROs (gtk.entry)
        # ------------------------------------------------

        # TODO - format will need to change for imperial versus metric (which is why they can't be constants)
        self.dro_long_format = "%2.4f"
        self.dro_medium_format = "%.1f"
        self.dro_short_format = "%.0F"
        self.dro_dwell_format = "%.2f"

        # main screen
        self.dro_list = ('x_dro', 'y_dro', 'z_dro', 'a_dro',
                         'feed_per_min_dro', 'spindle_rpm_dro', 'tool_dro',
                         'touch_z_dro', 'ets_height_dro', 'inject_dwell_dro',
                         'atc_manual_insert_dro', 'atc_auto_dro')

        # dictionary of DRO names, gtk.entry objects
        self.dro_list = dict(((i, self.builder.get_object(i))) for i in self.dro_list)
        dro_font_description  = pango.FontDescription('helvetica ultra-condensed 22')
        for name, dro in self.dro_list.iteritems():
            dro.modify_font(dro_font_description)
            dro.masked = False

        # DROs common to all conversational routines
        self.current_normal_z_feed_rate = ''
        self.conv_dro_list = (
            'conv_title_dro',
            'conv_work_offset_dro',
            'conv_tool_number_dro',
            'conv_rpm_dro',
            'conv_feed_dro',
            'conv_z_feed_dro',
            'conv_z_clear_dro')

        self.conv_dro_list = dict(((i, self.builder.get_object(i))) for i in self.conv_dro_list)
        conv_dro_font_description  = pango.FontDescription('helvetica ultra-condensed 22')

        for name, dro in self.conv_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        self.conv_dro_list['conv_title_dro'].modify_font(pango.FontDescription('helvetica ultra-condensed 18'))



        # Face DROs
        self.face_dro_list = (
            'face_x_start_dro',
            'face_x_end_dro',
            'face_y_start_dro',
            'face_y_end_dro',
            'face_z_start_dro',
            'face_z_end_dro',
            'face_z_doc_dro',
            'face_stepover_dro')

        self.face_dro_list = dict(((i, self.builder.get_object(i))) for i in self.face_dro_list)
        for name, dro in self.face_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        self.face_stepover_hint_label = self.builder.get_object('face_stepover_hint_text')

        # Profile DROs
        self.profile_dro_list = (
            'profile_z_doc_dro',
            'profile_z_end_dro',
            'profile_z_start_dro',
            'profile_stepover_dro',
            'profile_y_end_dro',
            'profile_y_start_dro',
            'profile_x_end_dro',
            'profile_x_start_dro',
            'profile_x_prfl_start_dro',
            'profile_y_prfl_end_dro',
            'profile_x_prfl_end_dro',
            'profile_y_prfl_start_dro',
            'profile_radius_dro',
            'profile_circ_z_doc_dro',
            'profile_circ_z_end_dro',
            'profile_circ_z_start_dro',
            'profile_circ_stepover_dro',
            'profile_circ_y_end_dro',
            'profile_circ_y_start_dro',
            'profile_circ_x_end_dro',
            'profile_circ_x_start_dro',
            'profile_circ_diameter_dro',
            'profile_x_center_dro',
            'profile_y_center_dro')

        self.profile_dro_list = dict(((i, self.builder.get_object(i))) for i in self.profile_dro_list)
        for name, dro in self.profile_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        self.profile_x_prfl_start_label = self.builder.get_object('profile_x_prfl_start_text')
        self.profile_x_prfl_end_label = self.builder.get_object('profile_x_prfl_end_text')
        self.profile_y_prfl_start_label = self.builder.get_object('profile_y_prfl_start_text')
        self.profile_y_prfl_end_label = self.builder.get_object('profile_y_prfl_end_text')
        self.profile_radius_label = self.builder.get_object('profile_radius_text')
        self.profile_circ_diameter_label = self.builder.get_object('profile_circ_diameter_text')
        self.profile_x_center_label = self.builder.get_object('profile_x_center_text')
        self.profile_y_center_label = self.builder.get_object('profile_y_center_text')

        self.profile_stepover_hint_label = self.builder.get_object('profile_stepover_hint_text')

        # Pocket-Rectangular DROs
        self.pocket_rect_dro_list = (
            'pocket_rect_x_start_dro',
            'pocket_rect_x_end_dro',
            'pocket_rect_y_start_dro',
            'pocket_rect_y_end_dro',
            'pocket_rect_z_start_dro',
            'pocket_rect_z_end_dro',
            'pocket_rect_z_doc_dro',
            'pocket_rect_stepover_dro',
            'pocket_rect_corner_radius_dro')

        self.pocket_rect_dro_list = dict(((i, self.builder.get_object(i))) for i in self.pocket_rect_dro_list)
        for name, dro in self.pocket_rect_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        self.pocket_rect_x_start_label       = self.builder.get_object('pocket_rect_x_start_text')
        self.pocket_rect_x_end_label         = self.builder.get_object('pocket_rect_x_end_text')
        self.pocket_rect_y_start_label       = self.builder.get_object('pocket_rect_y_start_text')
        self.pocket_rect_y_end_label         = self.builder.get_object('pocket_rect_y_end_text')
        self.pocket_rect_corner_radius_label = self.builder.get_object('pocket_rect_corner_radius_text')

        self.pocket_rect_stepover_hint_label = self.builder.get_object('pocket_rect_stepover_hint_text')

        # Pocket-Circular DROs
        self.pocket_circ_dro_list = (
            'pocket_circ_z_end_dro',
            'pocket_circ_z_start_dro',
            'pocket_circ_z_doc_dro',
            'pocket_circ_stepover_dro',
            'pocket_circ_diameter_dro')

        self.pocket_circ_dro_list = dict(((i, self.builder.get_object(i))) for i in self.pocket_circ_dro_list)
        for name, dro in self.pocket_circ_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        self.pocket_circ_x_center_label = self.builder.get_object('pocket_circ_x_center_text')
        self.pocket_circ_y_center_label = self.builder.get_object('pocket_circ_y_center_text')
        self.pocket_circ_diameter_label = self.builder.get_object('pocket_circ_diameter_text')

        self.pocket_circ_stepover_hint_label = self.builder.get_object('pocket_circ_stepover_hint_text')

        # Drill extras list - toggle for JA thread mill editing...
        self.drill_tap_extras = (
            'drill_tap_main_image',
            'drill_tap_detail_image',
            'drill_z_clear_text',
            'drill_tap_z_end_text'
        )
        self.drill_tap_extras = dict(((i, self.builder.get_object(i))) for i in self.drill_tap_extras)

        # Drill DROs
        self.drill_dro_list = (
            'drill_z_start_dro',
            'drill_peck_dro',
            'drill_z_end_dro',
            'drill_spot_tool_number_dro',
            'drill_spot_tool_doc_dro')

        self.drill_dro_list = dict(((i, self.builder.get_object(i))) for i in self.drill_dro_list)
        for name, dro in self.drill_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        self.drill_circular_dro_list = (
            'drill_tap_pattern_circular_holes_dro',
            'drill_tap_pattern_circular_start_angle_dro',
            'drill_tap_pattern_circular_diameter_dro',
            'drill_tap_pattern_circular_center_x_dro',
            'drill_tap_pattern_circular_center_y_dro')

        self.drill_circular_dro_list = dict(((i, self.builder.get_object(i))) for i in self.drill_circular_dro_list)
        for name, dro in self.drill_circular_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        drill_fields = ['spot_note',
                        'peck',
                        'spot_tool_number',
                        'spot_tool_doc',
                        'z_start']

        self.drill_labels = dict((f, self.get_obj('drill_%s_text' % f)) for f in drill_fields)

        self.drill_calc_font = pango.FontDescription('helvetica ultra-condensed 22')
        self.drill_through_hole_hint_label = self.builder.get_object('drill_through_hole_hint_text')
        self.drill_z_feed_per_rev_hint = self.builder.get_object('drill_z_feed_per_rev_text')
        self.drill_z_feed_per_rev_hint.set_visible(False)

        # Tap DROs
        self.tap_dro_list = (
            'tap_z_end_dro',
            'tap_dwell_dro',
            'tap_pitch_dro',
            'tap_tpu_dro')

        self.tap_dro_list = dict(((i, self.builder.get_object(i))) for i in self.tap_dro_list)
        for name, dro in self.tap_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        tap_fields = ['dwell_note',
                      'dwell_sec',
                      'dwell_travel',
                      'pitch',
                      'tpu',
                      'mult',
                      'rpm_pitch',
                      '60_2',
                      'dwell_travel_calc',
                      'rpm_feed']

        #Generate the dictionary from just the field names (no need to retype the full labels)
        self.tap_labels=dict((f, self.get_obj('tap_%s_text' % f)) for f in tap_fields)

        self.tap_hsep = self.builder.get_object('tap_hseparator')

        self.drill_pattern_notebook_page = 'pattern'

        # Thread Mill DROs
        # External
        thread_mill_ext_dro_list = (
            ##'thread_mill_ext_x_dro',
            ##'thread_mill_ext_y_dro',
            'thread_mill_ext_z_start_dro',
            'thread_mill_ext_z_end_dro',
            'thread_mill_ext_major_dia_dro',
            'thread_mill_ext_minor_dia_dro',
            'thread_mill_ext_doc_dro',
            'thread_mill_ext_passes_dro',
            'thread_mill_ext_pitch_dro',
            'thread_mill_ext_tpu_dro')

        self.thread_mill_ext_dro_list = dict((i,self.get_obj(i)) for i in thread_mill_ext_dro_list)
        for name, dro in self.thread_mill_ext_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        # Internal
        self.thread_mill_int_dro_list = (
            ##'thread_mill_int_x_dro',
            ##'thread_mill_int_y_dro',
            'thread_mill_int_z_start_dro',
            'thread_mill_int_z_end_dro',
            'thread_mill_int_major_dia_dro',
            'thread_mill_int_minor_dia_dro',
            'thread_mill_int_doc_dro',
            'thread_mill_int_passes_dro',
            'thread_mill_int_pitch_dro',
            'thread_mill_int_tpu_dro')

        self.thread_mill_int_dro_list = dict(((i, self.builder.get_object(i))) for i in self.thread_mill_int_dro_list)
        for name, dro in self.thread_mill_int_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        self.thread_mill_tpu_label = self.builder.get_object('thread_mill_tpu_text')
        self.thread_mill_pitch_label = self.builder.get_object('thread_mill_pitch_text')

        # thread data selector
        self.thread_chart_combobox = self.builder.get_object('thread_combobox')
        self.thread_chart_g20_liststore = gtk.ListStore(gobject.TYPE_STRING, gobject.TYPE_STRING)
        self.thread_chart_g21_liststore = gtk.ListStore(gobject.TYPE_STRING, gobject.TYPE_STRING)
        self.thread_chart_combobox.set_model(self.thread_chart_g20_liststore)

        cell = gtk.CellRendererText()
        self.thread_chart_combobox.pack_start(cell, True)
        self.thread_chart_combobox.add_attribute(cell, 'text', 0)
        cellview = self.thread_chart_combobox.get_child()
        cellview.set_displayed_row(0)

        self.refresh_thread_data_liststores()


        # Engrave DROs
        self.engrave_dro_list = (
            'engrave_text_dro',
            'engrave_x_base_dro',
            'engrave_y_base_dro',
            'engrave_z_start_dro',
            'engrave_height_dro',
            'engrave_z_doc_dro',
            'engrave_sn_start_dro')

        self.engrave_dro_list = dict(((i, self.builder.get_object(i))) for i in self.engrave_dro_list)
        for name, dro in self.engrave_dro_list.iteritems():
            dro.modify_font(conv_dro_font_description)

        self.engrave_sample_label = self.builder.get_object('engrave_sample_text')

        # --------------------------------------------
        # Call Scanner / Scope setup routines
        # --------------------------------------------

        self.scanner_gui_init()
        self.scope_gui_init()

        # --------------------------------------------
        # Labels
        # --------------------------------------------
        self.get_version_string()

        # dtg labels
        self.x_dtg_label = self.builder.get_object('x_dtg_label')
        self.y_dtg_label = self.builder.get_object('y_dtg_label')
        self.z_dtg_label = self.builder.get_object('z_dtg_label')
        self.a_dtg_label = self.builder.get_object('a_dtg_label')

        dtg_font_description = pango.FontDescription('helvetica ultra-condensed 22')
        self.x_dtg_label.modify_font(dtg_font_description)
        self.y_dtg_label.modify_font(dtg_font_description)
        self.z_dtg_label.modify_font(dtg_font_description)
        self.a_dtg_label.modify_font(dtg_font_description)

        # atc_labels
        self.atc_pocket_list = ('atc_carousel_0', 'atc_carousel_1', 'atc_carousel_2', 'atc_carousel_3', 'atc_carousel_4', 'atc_carousel_5',
                                'atc_carousel_6', 'atc_carousel_7', 'atc_carousel_8', 'atc_carousel_9', 'atc_carousel_10', 'atc_carousel_11')

        self.atc_pocket_list = dict(((i, self.builder.get_object(i))) for i in self.atc_pocket_list)

        for name, label in self.atc_pocket_list.iteritems():
                    label.modify_font(dtg_font_description)

        # ---------------------------------------------
        # overrides sliders (gtk.scale and gtk.adjustment)
        # and associated labels
        # ---------------------------------------------

        # the 'adjustment' object(value, lower bound, upper bound, step inc, page inc, page size)
        # is pre-set in the glade file.
        # Page inc and size should be zero to prevent accidental motion
        # mouse wheel events thrown out to prevent default gtk behavior
        self.feedrate_override_adjustment = self.builder.get_object("feedrate_override_adjustment")
        self.feedrate_override_scale = self.builder.get_object("feedrate_override_scale")
        self.feedrate_override_scale.connect("scroll-event", self.on_mouse_wheel_event)
        self.spindle_override_adjustment = self.builder.get_object("spindle_override_adjustment")
        self.spindle_override_scale = self.builder.get_object("spindle_override_scale")
        self.spindle_override_scale.connect("scroll-event", self.on_mouse_wheel_event)
        self.maxvel_override_adjustment = self.builder.get_object("maxvel_override_adjustment")
        self.maxvel_override_scale = self.builder.get_object("maxvel_override_scale")
        self.maxvel_override_scale.connect("scroll-event", self.on_mouse_wheel_event)
        self.jog_speed_adjustment = self.builder.get_object("jog_speed_adjustment")
        self.jog_speed_scale = self.builder.get_object("jog_speed_scale")
        self.jog_speed_scale.connect("scroll-event", self.on_mouse_wheel_event)
        self.feedrate_override_label = self.builder.get_object("feedrate_override_label")
        self.spindle_override_label = self.builder.get_object("spindle_override_label")
        self.maxvel_override_label = self.builder.get_object("maxvel_override_label")
        self.jog_speed_label = self.builder.get_object('jog_speed_label')
        self.active_gcodes_label = self.builder.get_object("active_gcodes_label")
        self.tlo_label = self.builder.get_object("tlo_label")
        self.feedrate_override_adjustment.set_value(100)
        self.spindle_override_adjustment.set_value(100)
        self.maxvel_override_adjustment.set_value(100)

        self.probe_x_plus_label  = self.builder.get_object('probe_x_plus_label')
        self.probe_x_minus_label = self.builder.get_object('probe_x_minus_label')
        self.probe_y_plus_label  = self.builder.get_object('probe_y_plus_label')
        self.probe_y_minus_label = self.builder.get_object('probe_y_minus_label')
        self.probe_z_minus_label = self.builder.get_object('probe_z_minus_label')

        self.probe_y_plus_a_label = self.builder.get_object('probe_y_plus_a_label')
        self.probe_y_plus_b_label = self.builder.get_object('probe_y_plus_b_label')
        self.probe_y_plus_c_label = self.builder.get_object('probe_y_plus_c_label')

        self.probe_x_plus_label.modify_font(self.drill_calc_font)
        self.probe_x_minus_label.modify_font(self.drill_calc_font)
        self.probe_y_plus_label.modify_font(self.drill_calc_font)
        self.probe_y_minus_label.modify_font(self.drill_calc_font)
        self.probe_z_minus_label.modify_font(self.drill_calc_font)
        self.probe_y_plus_a_label.modify_font(self.drill_calc_font)
        self.probe_y_plus_b_label.modify_font(self.drill_calc_font)
        self.probe_y_plus_c_label.modify_font(self.drill_calc_font)

        self.setup_gcode_marks()

        # ------------------------------------------------
        # Check buttons
        # ------------------------------------------------

        self.checkbutton_list = ('enable_soft_keyboard_checkbutton',
                                 'use_manual_toolchange_checkbutton', 'use_atc_checkbutton',
                                 'passive_probe_radiobutton', 'active_probe_radiobutton',
                                 'enable_scanner_checkbutton', 'disable_home_switches_checkbutton',
                                 'g30m998_move_z_only_checkbutton', 'enable_usbio_checkbutton',
                                 'enable_injector_checkbutton', 'enable_door_sw_checkbutton',
                                 'tap_2x_checkbutton', 'fourth_axis_homing_checkbutton',
                                 'engrave_left_radiobutton', 'engrave_center_radiobutton',
                                 'engrave_right_radiobutton',
                                 'thread_mill_right_radiobutton', 'thread_mill_left_radiobutton')

        self.checkbutton_list = dict(((i, self.builder.get_object(i))) for i in self.checkbutton_list)



        # -----------------------------------------------------
        # Persistent storage of machine settings, user-entered vals on conv. pages
        # Redis settings are in redis.conf file
        # actual flat file is rdb.dump, currently being saved in config dir.
        # -----------------------------------------------------

        # spindle type and min/max for high speed spindle type
        spindle_type_str = self.redis.hget('machine_prefs', 'spindle_type');

        if spindle_type_str == None:
            print 'no spindle type found in redis defaulting to standard'
            spindle_type_str = '0'

        self.spindle_type = int(spindle_type_str)
        if self.spindle_type < SPINDLE_TYPE_STANDARD or self.spindle_type > SPINDLE_TYPE_HISPEED:
            self.spindle_type = SPINDLE_TYPE_STANDARD
        print 'spindle type: %d' % self.spindle_type
        self.hal['spindle-type'] = self.spindle_type

        speed_str = self.redis.hget('machine_prefs', 'spindle_hispeed_min');
        if speed_str == None:
            #print 'no spindle_hispeed_min found in redis defaulting to 8000'
            speed_str = '1000'
        self.spindle_hispeed_min = int(speed_str)
        #print 'spindle hispeed min: %d' % self.spindle_hispeed_min
        self.hal['spindle-hispeed-min'] = self.spindle_hispeed_min

        self.spindle_hispeed_min_entry = self.builder.get_object('spindle_hispeed_min_entry')
        self.spindle_hispeed_min_entry.set_text('%d' % self.spindle_hispeed_min)

        speed_str = self.redis.hget('machine_prefs', 'spindle_hispeed_max');
        if speed_str == None:
            #print 'no spindle_hispeed_max found in redis defaulting to 24000'
            speed_str = '24000'
        self.spindle_hispeed_max = int(speed_str)
        #print 'spindle hispeed max: %d' % self.spindle_hispeed_max
        self.hal['spindle-hispeed-max'] = self.spindle_hispeed_max

        self.spindle_hispeed_max_entry = self.builder.get_object('spindle_hispeed_max_entry')
        self.spindle_hispeed_max_entry.set_text('%s' % self.spindle_hispeed_max)

        # spindle type combobox
        self.spindle_type_liststore = gtk.ListStore(str)
        self.spindle_type_combobox = self.builder.get_object("spindle_type_combobox")
        self.spindle_type_combobox.set_model(self.spindle_type_liststore)
        cell = gtk.CellRendererText()
        self.spindle_type_combobox.pack_start(cell, True)
        self.spindle_type_combobox.add_attribute(cell, 'text', 0)
        self.spindle_type_liststore.append(['Standard'])
        self.spindle_type_liststore.append(['Speeder'])
        self.spindle_type_liststore.append(['High-speed'])
        self.spindle_type_combobox.set_active(self.spindle_type)

        self.make_hispeed_min_max_visible(self.spindle_type)

        # touchscreen
        # remember! Redis stores strings, not bools
        self.touchscreen_enabled = self.redis.hget('machine_prefs', 'touchscreen') == "True"
        self.checkbutton_list['enable_soft_keyboard_checkbutton'].set_active(self.touchscreen_enabled)

        self.probe_active_high = self.redis.hget('machine_prefs', 'probe_active_high') == "True"
        self.hal['probe-active-high'] = self.probe_active_high
        if self.probe_active_high:
            self.checkbutton_list['active_probe_radiobutton'].set_active(True)
        else:
            self.checkbutton_list['passive_probe_radiobutton'].set_active(True)

        # 4th axis homing
        self.fourth_axis_homing_enabled = self.redis.hget('machine_prefs', 'fourth_axis_homing_enabled') == "True"
        # set 4th axis homing parameters
        self.set_4th_axis_homing_parameters(self.fourth_axis_homing_enabled)
        # set the checkbutton status
        self.checkbutton_list['fourth_axis_homing_checkbutton'].set_active(self.fourth_axis_homing_enabled)

        try:
            self.ets_height = float(self.redis.hget('machine_prefs', 'setter_height'))
        except:
            self.ets_height = (80/25.4)
            self.redis.hset('machine_prefs', 'setter_height', self.ets_height)

        self.gcodes_display = tormach_file_util.active_codes_display()
        self.notebook_settings_fixed = self.builder.get_object('notebook_settings_fixed')
        self.notebook_settings_fixed.put(self.gcodes_display.sw, 10, 10)

        self.ef_num_rows = self.setup_font_selector()

        self.setup_filechooser()

        # set jog increment
        self.jog_increment = 0.0001
        # set jog speed
        ini_jog_speed = (
            inifile.find("DISPLAY", "DEFAULT_LINEAR_VELOCITY")
            or inifile.find("TRAJ", "DEFAULT_LINEAR_VELOCITY")
            or inifile.find("TRAJ", "DEFAULT_VELOCITY")
            or 1.0)
        self.jog_speed = (float(ini_jog_speed))
        self.jog_speeds = [float(inifile.find("AXIS_%d" % ind, "MAX_JOG_VELOCITY_UPS")) for ind in range(4)]
        # set jog speed percentage
        self.jog_override_pct = 0.4
        # default to continuous jog mode
        self.jog_mode = linuxcnc.JOG_CONTINUOUS
        self.keyboard_jog_mode = linuxcnc.JOG_CONTINUOUS
        # initial jog percent to 40
        self.jog_speed_adjustment.set_value(self.jog_override_pct * 100)



        self.prev_jog_ring_speed = 0.0

        # keyboard jogging - connect keypress to callbacks
        self.window.connect("key_press_event", self.on_key_press_or_release)
        self.window.connect("key_release_event", self.on_key_press_or_release)


        # mode/state tracking (debug only)
        self.prev_lcnc_task_mode = -1
        self.prev_lcnc_interp_state = -1
        self.prev_task_state = -1

        # initialize limit states used in periodic function
        self.prev_status_limit = {0:0, 1:0, 2:0, 3:0}
        self.display_limit_msg = {0:True, 1:True, 2:True, 3:True}

        # ---------------------------------------------------
        # MDI line (gtk.entry)
        # ---------------------------------------------------

        # global MDI history list of typed in commands
        # arrow up/down inside edit displays
        self.mdi_history = []
        self.mdi_history_index = -1
        try:
            hist_length = self.redis.llen('mdi_history')
            for i in range(0, hist_length):
                self.mdi_history.append(self.redis.lpop('mdi_history'))
            self.mdi_history_index = int(self.redis.hget('machine_prefs', 'mdi_history_index'))
        except:
            self.error_handler.write("Retrieval of MDI history failed.", ALARM_LEVEL_DEBUG)
            pass
        self.mdi_history_max_entry_count = 100
        self.mdi_line = self.builder.get_object("mdi_line")
        self.mdi_line_masked = 0
        mid_font_description = pango.FontDescription('helvetica ultra-condensed 18')
        self.mdi_line.modify_font(mid_font_description)
        self.mdi_line.modify_text(gtk.STATE_NORMAL, gtk.gdk.Color('#C3C9CA'))

        # ---------------------------------------------------
        # tool change type and zbot atc init
        # ---------------------------------------------------

        self.atc = zbot_atc.zbot_atc(self.config,self.status, self.command, self.issue_mdi, self.hal, self.redis, self.atc_pocket_list, self.dro_list, self.program_running,self.notebook, self.error_handler)

        # connect timer to status poll periodic function
        gobject.timeout_add(50, self.periodic_status)

        # this counter is used to call the slower periodic function
        self.periodic_loopcount = 0

        # get user's home directory
        self.home_dir = os.getenv('HOME')

        # holds path to currently loaded gcode file
        # slow periodic polls for changes and reloads if appropriate
        self.set_current_gcode_path('')


        try:
            tc_type = self.redis.hget('machine_prefs', 'toolchange_type')
            if tc_type == MILL_TOOLCHANGE_TYPE_REDIS_ZBOT:
                self.atc.enable()
                self.show_atc_diagnostics()
                self.checkbutton_list['use_atc_checkbutton'].set_active(True)
                change_z = float(self.redis.hget('zbot_slot_table', 'tool_change_z'))
                if change_z < -1.5 and change_z > -3.5:
                    self.set_image('set_tool_change_z_image', 'Set-TC-POS-Green.png')
            else:
                self.atc.disable()
                self.hide_atc_diagnostics()
                self.checkbutton_list['use_manual_toolchange_checkbutton'].set_active(True)
        except:
            self.error_handler.write("No toolchange_type found in redis machine prefs database", ALARM_LEVEL_DEBUG)
            self.atc.disable()
            self.checkbutton_list['use_manual_toolchange_checkbutton'].set_active(True)


        # -----------------------------------------
        # tool table init (gtk.treeview)
        # -----------------------------------------
        # using a treeview/liststore for the tool table, on the tools page of the notebook
        self.tool_liststore = gtk.ListStore(int, str, str, str)

        # Create a TreeView and let it know about the model we created above
        self.treeview = gtk.TreeView(self.tool_liststore)
        self.treeselection = self.treeview.get_selection()
        self.treeselection.set_mode(gtk.SELECTION_SINGLE)

        self.tool_table_filename = inifile.find("EMCIO", "TOOL_TABLE") or ""
        if self.tool_table_filename == "":
            self.tool_table_filename = "~/mill_data/tool.tbl"
        if self.tool_table_filename.startswith('~/'):
            self.tool_table_filename = os.path.join(os.getenv('HOME'), self.tool_table_filename[2:])
        self.tool_table_file_mtime = os.stat(self.tool_table_filename).st_mtime
        self.refresh_tool_liststore(True)

        # create columns
        self.tool_num_column           = gtk.TreeViewColumn('Tool')
        self.tool_description_column   = gtk.TreeViewColumn('Description')
        self.tool_diameter_column      = gtk.TreeViewColumn('Diameter')
        self.tool_length_column        = gtk.TreeViewColumn('Length')


        # add columns to treeview
        self.treeview.append_column(self.tool_num_column)
        self.treeview.append_column(self.tool_description_column)
        self.treeview.append_column(self.tool_diameter_column)
        self.treeview.append_column(self.tool_length_column)

        tool_col_renderer = gtk.CellRendererText()
        tool_col_renderer.set_property('editable', False)
        tool_col_renderer.set_property('cell-background', '#E1B3B7')
        self.tool_num_column.pack_start(tool_col_renderer, True)
        self.tool_num_column.set_attributes(tool_col_renderer, text=0)


        tool_description_renderer = gtk.CellRendererText()
        tool_description_renderer.set_property('editable', True)
        tool_description_renderer.set_property('cell-background', '#D5E1B3')
        self.tool_description_column.pack_start(tool_description_renderer, True)
        self.tool_description_column.set_attributes(tool_description_renderer, text=1)
        self.tool_description_column.set_sizing(gtk.TREE_VIEW_COLUMN_FIXED)
        self.tool_description_column.set_fixed_width(250)
        tool_description_renderer.connect( 'edited', self.on_tool_description_column_edited, self.tool_liststore )
        tool_description_renderer.connect( 'editing-started', self.on_tool_description_column_editing_started)

        tool_diameter_renderer = gtk.CellRendererText()
        tool_diameter_renderer.set_property('editable', True)
        tool_diameter_renderer.set_property('cell-background', '#D6D76C')
        self.tool_diameter_column.pack_start(tool_diameter_renderer, True)
        self.tool_diameter_column.set_attributes(tool_diameter_renderer, text=2)
        tool_diameter_renderer.connect( 'edited', self.on_tool_diameter_column_edited, self.tool_liststore )
        tool_diameter_renderer.connect( 'editing-started', self.on_tool_diameter_column_editing_started)

        tool_length_renderer = gtk.CellRendererText()
        tool_length_renderer.set_property('editable', True)
        tool_length_renderer.set_property('cell-background', '#B3E1D7')
        self.tool_length_column.pack_start(tool_length_renderer, True)
        self.tool_length_column.set_attributes(tool_length_renderer, text=3)
        tool_length_renderer.connect( 'edited', self.on_tool_length_column_edited, self.tool_liststore )
        tool_length_renderer.connect( 'editing-started', self.on_tool_length_column_editing_started)


        # show in notebook

        # create a scrolled window to hold the treeview
        self.scrolled_window_tool_table = gtk.ScrolledWindow()
        self.scrolled_window_tool_table.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        self.tool_offsets_fixed.put(self.scrolled_window_tool_table, 515, 10)
        self.scrolled_window_tool_table.add(self.treeview)
        self.scrolled_window_tool_table.set_size_request(455, 345)

        # -----------------------------------------
        # drill table init (gtk.treeview)
        # -----------------------------------------
        drill_font = pango.FontDescription('helvetica ultra-condensed 18')
        drill_i_font = pango.FontDescription('helvetica ultra-condensed 16')

        self.drill_liststore = gtk.ListStore(str, str, str)


        for id_cnt  in range(1, self.DRILL_TABLE_ROWS + 1):
            self.drill_liststore.append([id_cnt, '', ''])

        self.drill_treeview = gtk.TreeView(self.drill_liststore)

        self.drill_i_column  = gtk.TreeViewColumn()
        self.drill_x_column  = gtk.TreeViewColumn('')
        self.drill_y_column  = gtk.TreeViewColumn('')

        self.drill_treeview.append_column(self.drill_i_column)
        self.drill_treeview.append_column(self.drill_x_column)
        self.drill_treeview.append_column(self.drill_y_column)

        self.drill_treeview.set_rules_hint(True)
        self.drill_treeview.set_headers_visible(False)
        self.drill_treeview.set_grid_lines(gtk.TREE_VIEW_GRID_LINES_BOTH)

        drill_i_renderer = gtk.CellRendererText()
        drill_i_renderer.set_property('editable', False)
        drill_i_renderer.set_property('cell-background', '#EEBBBB')
        drill_i_renderer.set_property('font-desc', drill_i_font)
        drill_i_renderer.set_property('xalign',0.5);
        drill_i_renderer.set_property('yalign',1);
        drill_i_renderer.set_property('height',28);
        self.drill_i_column.set_sizing(gtk.TREE_VIEW_COLUMN_FIXED)
        self.drill_i_column.set_fixed_width(30)
        self.drill_i_column.pack_start(drill_i_renderer, True)
        self.drill_i_column.set_attributes(drill_i_renderer, text=0)

        drill_x_renderer = gtk.CellRendererText()
        drill_x_renderer.set_property('editable', True)
        drill_x_renderer.set_property('font-desc', drill_font)
        drill_x_renderer.set_property('xalign',0.8);
        drill_x_renderer.set_property('yalign',1);
        drill_x_renderer.set_property('height',28);
#       drill_x_renderer.set_property('rise',12);
#       drill_x_renderer.set_property('rise-set',True);
        self.drill_x_column.set_sizing(gtk.TREE_VIEW_COLUMN_FIXED)
        self.drill_x_column.set_fixed_width(105)
        self.drill_x_column.pack_start(drill_x_renderer, True)
        self.drill_x_column.set_attributes(drill_x_renderer, text=1)
        drill_x_renderer.connect('edited', self.on_drill_x_column_edited, self.drill_liststore)

        drill_y_renderer = gtk.CellRendererText()
        drill_y_renderer.set_property('editable', True)
        drill_y_renderer.set_property('font-desc', drill_font)
        drill_y_renderer.set_property('xalign',0.8);
        drill_y_renderer.set_property('yalign',1);
        drill_y_renderer.set_property('height',28);
#       drill_y_renderer.set_property('rise',12);
        self.drill_y_column.set_fixed_width(105)
        self.drill_y_column.pack_start(drill_y_renderer, True)
        self.drill_y_column.set_attributes(drill_y_renderer, text=2)
        drill_y_renderer.connect('edited', self.on_drill_y_column_edited, self.drill_liststore)

        drill_x_renderer.connect('editing-started', self.on_drill_x_column_editing_started, drill_font)
        drill_y_renderer.connect('editing-started', self.on_drill_y_column_editing_started, drill_font)
        self.drill_x_renderer = drill_x_renderer
        self.drill_y_renderer = drill_y_renderer

        # show in notebook

        # create a scrolled window to hold the treeview
        self.scrolled_window_drill_table = gtk.ScrolledWindow()
        self.scrolled_window_drill_table.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        self.conv_drill_tap_pattern_notebook_fixed.put(self.scrolled_window_drill_table, 7, 32)
        self.scrolled_window_drill_table.add_with_viewport(self.drill_treeview)
        self.scrolled_window_drill_table.set_size_request(270, 270)

        # restore last used values on conversational screens
        self.restore_conv_parameters()

        # update the step-over hints
        self._update_stepover_hints()

        # update the step-over hints



        # -----------------------------------------
        # Work Offset table init (gtk.treeview)
        # -----------------------------------------
        self.work_font = work_font = \
                         pango.FontDescription('helvetica ultra-condensed 14')

        self.work_liststore = gtk.ListStore(str, str, str, str, str, str, str)




        # Create a TreeView and let it know about the model we created above
        self.work_treeview = gtk.TreeView(self.work_liststore)

        work_id_column = gtk.TreeViewColumn('')
        work_id_label = gtk.Label('ID')
        work_id_label.modify_font(work_font)
        work_id_column.set_widget(work_id_label)
        work_id_label.show()

        work_x_column  = gtk.TreeViewColumn('')
        work_x_label = gtk.Label('X')
        work_x_label.modify_font(work_font)
        work_x_column.set_widget(work_x_label)
        work_x_label.show()

        work_y_column  = gtk.TreeViewColumn('')
        work_y_label = gtk.Label('Y')
        work_y_label.modify_font(work_font)
        work_y_column.set_widget(work_y_label)
        work_y_label.show()

        work_z_column  = gtk.TreeViewColumn('')
        work_z_label = gtk.Label('Z')
        work_z_label.modify_font(work_font)
        work_z_column.set_widget(work_z_label)
        work_z_label.show()

        work_a_column  = gtk.TreeViewColumn('')
        work_a_label = gtk.Label('A')
        work_a_label.modify_font(work_font)
        work_a_column.set_widget(work_a_label)
        work_a_label.show()

        self.work_treeview.append_column(work_id_column)
        self.work_treeview.append_column(work_x_column)
        self.work_treeview.append_column(work_y_column)
        self.work_treeview.append_column(work_z_column)
        self.work_treeview.append_column(work_a_column)

        self.work_treeview.set_rules_hint(True)

        work_id_renderer = gtk.CellRendererText()
        work_id_renderer.set_property('editable', False)
        work_id_renderer.set_property('font-desc', work_font)
        work_id_renderer.set_property('cell-background', '#E1B3B7')
        work_id_renderer.set_property('width',80)
        work_id_column.pack_start(work_id_renderer, True)
        work_id_column.set_attributes(work_id_renderer, text=0)

        work_x_renderer = gtk.CellRendererText()
        work_x_renderer.set_property('editable', True)
        work_x_renderer.set_property('font-desc', work_font)
        work_x_renderer.set_property('xalign',0.8)
        work_x_renderer.set_property('width',100)
        work_x_column.pack_start(work_x_renderer, True)
        work_x_column.set_attributes(work_x_renderer, text=1, foreground=5, background=6)

        work_y_renderer = gtk.CellRendererText()
        work_y_renderer.set_property('editable', True)
        work_y_renderer.set_property('font-desc', work_font)
        work_y_renderer.set_property('xalign',0.8)
        work_y_renderer.set_property('width',100)
        work_y_column.pack_start(work_y_renderer, True)
        work_y_column.set_attributes(work_y_renderer, text=2, foreground=5, background=6)


        work_z_renderer = gtk.CellRendererText()
        work_z_renderer.set_property('editable', True)
        work_z_renderer.set_property('font-desc', work_font)
        work_z_renderer.set_property('xalign',0.8)
        work_z_renderer.set_property('width',100)
        work_z_column.pack_start(work_z_renderer, True)
        work_z_column.set_attributes(work_z_renderer, text=3, foreground=5, background=6)

        work_a_renderer = gtk.CellRendererText()
        work_a_renderer.set_property('editable', True)
        work_a_renderer.set_property('font-desc', work_font)
        work_a_renderer.set_property('xalign',0.8)
        work_a_renderer.set_property('width',100)
        work_a_column.pack_start(work_a_renderer, True)
        work_a_column.set_attributes(work_a_renderer, text=4, foreground=5, background=6)

        # Callbacks for when a work offset has begun being edited;
        # args are next column name and how many to increment the row
        # number by
        work_x_renderer.connect( 'editing-started',
                                 self.on_work_column_editing_started,
                                 work_y_column, 0)
        work_y_renderer.connect( 'editing-started',
                                 self.on_work_column_editing_started,
                                 work_z_column, 0)
        work_z_renderer.connect( 'editing-started',
                                 self.on_work_column_editing_started,
                                 work_a_column, 0)
        work_a_renderer.connect( 'editing-started',
                                 self.on_work_column_editing_started,
                                 work_x_column, 1)

        # Callbacks for when a work offset has finished being edited;
        # arg is the axis letter
        work_x_renderer.connect( 'edited', self.on_work_column_edited,
                                 self.work_liststore, 'x' )
        work_y_renderer.connect( 'edited', self.on_work_column_edited,
                                 self.work_liststore, 'y' )
        work_z_renderer.connect( 'edited', self.on_work_column_edited,
                                 self.work_liststore, 'z' )
        work_a_renderer.connect( 'edited', self.on_work_column_edited,
                                 self.work_liststore, 'a' )

        # show in notebook

        # create a scrolled window to hold the treeview
        self.scrolled_window_work_table = gtk.ScrolledWindow()
        self.scrolled_window_work_table.set_policy(gtk.POLICY_NEVER, gtk.POLICY_AUTOMATIC)

        self.work_offsets_fixed.put(self.scrolled_window_work_table, 10, 10)
        self.scrolled_window_work_table.add_with_viewport(self.work_treeview)
        self.scrolled_window_work_table.set_size_request(500, 305)

        # Keep track of work offset probes
        self.work_probe_in_progress = False


        """
        # restore last used values on conversational screens
        self.restore_conv_parameters()
        """

        # restore last used values on conversational screens
        self.restore_conv_parameters()


        # end job table init (gtk.treeview)
        # -----------------------------------------


        self.hal['spindle-range'] = self.redis.hget('machine_prefs', 'spindle_range') == "hi"

        if self.hal['spindle-range']:
            # high
            self.set_image('spindle_range_image', 'Spindle_Range_HI_Highlight.png')
        else:
            # low
            self.set_image('spindle_range_image', 'Spindle_Range_LO_Highlight.png')

        # limit switch enable
        self.home_switches_enabled = True
        try:
            redis_response = self.redis.hget('machine_prefs', 'home_switches_enabled')
            if redis_response == 'True' or redis_response == None:
                self.home_switches_enabled = True
            else:
                self.home_switches_enabled = False
        except:
            self.error_handler.write("exception looking for 'machine_prefs', 'home_switches_enabled' in redis, defaulting to True", ALARM_LEVEL_LOW)
            # write to redis to avoid future messages
            self.redis.hset('machine_prefs', 'home_switches_enabled', 'True')
        self.checkbutton_list['disable_home_switches_checkbutton'].set_active(not self.home_switches_enabled)
        self.hal['home-switch-enable'] = self.home_switches_enabled

        # g30/m998 move in Z only
        self.g30m998_move_z_only = True
        try:
            redis_response = self.redis.hget('machine_prefs', 'g30m998_move_z_only')
            if redis_response == 'True' or redis_response == None:
                self.g30m998_move_z_only = True
            else:
                self.g30m998_move_z_only = False
        except:
            self.error_handler.write("exception looking for 'machine_prefs', 'g30m998_move_z_only' in redis, defaulting to True", ALARM_LEVEL_LOW)
            # write to redis to avoid future messages
            self.redis.hset('machine_prefs', 'g30m998_move_z_only', 'True')
        self.checkbutton_list['g30m998_move_z_only_checkbutton'].set_active(self.g30m998_move_z_only)

        try:
            self.usbio_enabled = self.redis.hget('machine_prefs', 'usbio_enabled') == 'True'
        except:
            self.error_handler.write("exception looking for 'machine_prefs', 'usbio enabled' in redis, defaulting to False", ALARM_LEVEL_LOW)
            # write to redis to avoid future messages
            self.redis.hset('machine_prefs', 'usbio_enabled', 'False')
        self.checkbutton_list['enable_usbio_checkbutton'].set_active(self.usbio_enabled)

        self.injector_enabled = False
        try:
            self.injector_enabled = self.redis.hget('machine_prefs', 'injector_enabled') == 'True'
        except:
            self.error_handler.write("exception looking for 'machine_prefs', 'injector_enabled' in redis, defaulting to False", ALARM_LEVEL_LOW)
            # write to redis to avoid future messages
            self.redis.hset('machine_prefs', 'injector_enabled', 'False')
        self.checkbutton_list['enable_injector_checkbutton'].set_active(self.injector_enabled)

        try:
            self.injector_dwell = float(self.redis.hget('machine_prefs', 'injector_dwell'))
        except:
            #self.error_handler.write("exception looking for 'machine_prefs', 'injector_dwell' in redis, defaulting to 20 sec.", ALARM_LEVEL_LOW)
            # write to redis to avoid future messages
            self.redis.hset('machine_prefs', 'injector_dwell', '20')
            self.injector_dwell = 20.

        self.dro_list['inject_dwell_dro'].set_text(self.dro_medium_format % self.injector_dwell)

        self.door_sw_enabled = False
        self.hal['enc-door-switch-configured'] = 0
        try:
            self.door_sw_enabled = self.redis.hget('machine_prefs', 'door_sw_enabled') == 'True'
        except:
            self.error_handler.write("exception looking for 'machine_prefs', 'door_sw_enabled' in redis, defaulting to False", ALARM_LEVEL_LOW)
            # write to redis to avoid future messages
            self.redis.hset('machine_prefs', 'door_sw_enabled', 'False')
        self.checkbutton_list['enable_door_sw_checkbutton'].set_active(self.door_sw_enabled)

        try:
            disable_door_sw_checkbutton = self.redis.hget('machine_prefs', 'door_sw_hard_enabled') == 'True'
        except:
            self.error_handler.write("exception looking for 'machine_prefs', 'door_sw_hard_enabled' in redis, defaulting to False", ALARM_LEVEL_LOW)
            # write to redis to avoid future messages
            self.redis.hset('machine_prefs', 'door_sw_hard_enabled', 'False')

        if disable_door_sw_checkbutton:
            self.door_sw_enabled = True
            self.checkbutton_list['enable_door_sw_checkbutton'].set_visible(False)

        if self.door_sw_enabled:
            self.hal['enc-door-switch-configured'] = 1

        speed_str = self.redis.hget('machine_prefs', 'enc_door_open_max_rpm');
        if speed_str == None:
            print 'no enc_door_open_max_rpm found in redis defaulting to 1000'
            speed_str = '1000'
        self.enc_open_door_max_rpm = int(speed_str)
        print 'enclosure door open max rpm: %d' % self.enc_open_door_max_rpm
        self.hal['enc-door-open-max-rpm'] = self.enc_open_door_max_rpm

        # numlock status
        self.numlock_on = True
        try:
            redis_response = self.redis.hget('machine_prefs', 'numlock_on')
            if redis_response == 'True' or redis_response == None:
                self.numlock_on = True
            else:
                self.numlock_on = False
        except:
            #self.error_handler.write("exception looking for 'machine_prefs', 'numlock_on' in redis, defaulting to True", ALARM_LEVEL_LOW)
            # write to redis to avoid future messages
            self.redis.hset('machine_prefs', 'numlock_on', 'True')
        #self.checkbutton_list['numlock_on'].set_active(self.numlock_on)
        #self.set_numlock(self.numlock_on)

        # NetBIOS name
        self.netbios_name = get_netbios_name(netbios_name_conf_file)
        self.netbios_name_widget = self.builder.get_object('netbios_name')
        self.netbios_name_widget.set_text(self.netbios_name)

        # Due to what we think is a race condition between the init method and gtk's realization of the
        # notebook widget, this call doesn't always work
        self.notebook.connect("realize", self.show_enabled_notebook_tabs)

        self.alt_keyboard_shortcuts = (
            (gtk.keysyms.r, self.button_list['cycle_start']),
            (gtk.keysyms.R, self.button_list['cycle_start']),
            (gtk.keysyms.s, self.button_list['stop']),
            (gtk.keysyms.S, self.button_list['stop']),
            (gtk.keysyms.f, self.button_list['coolant']),
            (gtk.keysyms.F, self.button_list['coolant'])
        )

        self.ctrl_keyboard_shortcuts = (
            #(gtk.keysyms.a, self.button_list['foo']),
            #(gtk.keysyms.b, self.button_list['bar']),
            #(gtk.keysyms.c, self.button_list['baz'])
        )

        self._update_size_of_gremlin()

        # show the window here, not in the instantiation of the mill gui object
        self.window.show_all()

        # now we can hide whatever we want
        # 440 specific stuff
        self.is_440 = False
        if '440' in config:
            self.do_440_setup()

        self.show_or_hide_x_limit_led()
        self.show_or_hide_door_sw_led()


    def do_440_setup(self):
        # no reverse spindle available - hide ccw button and move stop and cw over to the right
        self.is_440 = True
        self.button_list['ccw'].hide()
        self.button_list['spindle_stop'].x = 690
        self.button_list['cw'].x = 759
        self.fixed.move(self.button_list['spindle_stop'], self.button_list['spindle_stop'].x, self.button_list['spindle_stop'].y)
        self.fixed.move(self.button_list['cw'], self.button_list['cw'].x, self.button_list['cw'].y)


        # limit switches always wired with X and Y in series
        # and former X input as enclosure door switch
        # force True and hide check box on Settings tab
        self.door_sw_enabled = True
        self.hal['enc-door-switch-configured'] = 1
        self.checkbutton_list['enable_door_sw_checkbutton'].hide()
        self.builder.get_object('enable_door_sw_text').hide()

        # make sure no warning on ref
        self.redis.hset('machine_prefs', 'display_door_sw_x_ref_warning', 'False')

        # no HSS spindle option
        self.builder.get_object('spindle_type_label').hide()
        self.builder.get_object('spindle_type_combobox').hide()

        # no injection molder or homing kit due to leadshine mx board input polarity
        self.builder.get_object('fourth_axis_homing_checkbutton').hide()
        self.builder.get_object('fourth_axis_homing_text').hide()
        self.builder.get_object('enable_injector_checkbutton').hide()
        self.builder.get_object('enable_injector_text').hide()

        # hard coded to passive probe only due to leadshine mx board input
        self.probe_active_high = False
        self.redis.hset('machine_prefs', 'probe_active_high', self.probe_active_high)
        self.hal['probe-active-high'] = self.probe_active_high
        self.builder.get_object('passive_probe_radiobutton').hide()
        self.builder.get_object('passive_probe_text').hide()
        self.builder.get_object('active_probe_radiobutton').hide()
        self.builder.get_object('active_probe_text').hide()

        # no tapping
        self.builder.get_object('drill_tap_tab_label').set_text("Drill")
        self.button_list['drill_tap'].hide()
        self.conversational.routine_names['routines']['Pattern Tap']['edit'] = None
        self.conversational.routine_names['routines']['Circular Tap']['edit'] = None
        self.conversational.routine_names['routines']['Pattern Drill']['conv'] = list(('Drill',))
        self.conversational.routine_names['routines']['Circular Drill']['conv'] =  list(('Drill',))
        self.conversational.routine_names['routines']['External Thread Mill']['conv'] = list(('Thread Mill','Drill'))
        self.conversational.routine_names['routines']['Internal Thread Mill']['conv'] = list(('Thread Mill','Drill'))


        # ATC has 8 tools, not 10
        # NB: 2200 carousel will have 12, there are already 12 labels in the glade file but #11 and 12 are not visible.
        self.set_image('atc_tray_image', 'ATC_440_Tray.png')
        self.atc_pocket_list['atc_carousel_8'].hide()
        self.atc_pocket_list['atc_carousel_9'].hide()
        self.atc_fixed.move(self.atc_pocket_list['atc_carousel_0'], 649, 186)
        self.atc_fixed.move(self.atc_pocket_list['atc_carousel_1'], 605, 60 )
        self.atc_fixed.move(self.atc_pocket_list['atc_carousel_2'], 479, 17 )
        self.atc_fixed.move(self.atc_pocket_list['atc_carousel_3'], 354, 60 )
        self.atc_fixed.move(self.atc_pocket_list['atc_carousel_4'], 310, 186)
        self.atc_fixed.move(self.atc_pocket_list['atc_carousel_5'], 356, 312)
        self.atc_fixed.move(self.atc_pocket_list['atc_carousel_6'], 480, 354)
        self.atc_fixed.move(self.atc_pocket_list['atc_carousel_7'], 605, 312)


    def make_hispeed_min_max_visible(self, spindle_type):
        # if hispeed spindle selected - make min/max fields visible
        # ALWAYS HIDE THESE
        if False and spindle_type == SPINDLE_TYPE_HISPEED:
            self.builder.get_object("hispeed_min_label").set_visible(True)
            self.builder.get_object("hispeed_max_label").set_visible(True)
            self.builder.get_object("spindle_hispeed_min_entry").set_visible(True)
            self.builder.get_object("spindle_hispeed_max_entry").set_visible(True)
        else:
            self.builder.get_object("hispeed_min_label").set_visible(False)
            self.builder.get_object("hispeed_max_label").set_visible(False)
            self.builder.get_object("spindle_hispeed_min_entry").set_visible(False)
            self.builder.get_object("spindle_hispeed_max_entry").set_visible(False)

    def setup_key_sets(self):
        """ Add custom disable jog pages for Mill UI when setting up key sets"""
        # Call parent setup function in base class
        TormachUIBase.setup_key_sets(self)

        # Define page list here since some values are redefined
        self.disable_jog_pages = set([
            FILE_PAGE,
            SETTINGS_PAGE,
            CONVERSATIONAL_PAGE,
            MILL_STATUS_PAGE,
        ])

    def scanner_gui_init(self):
        # Define scanner fixed regions for later use
        self.scanner_fixed       = self.builder.get_object("scanner_fixed")
        # FIXME move this gtkimage to the glade file?
        self.scanner_common_camera_image = self.builder.get_object("scanner_common_camera_image")

        self.scanner = None
        self.scanner_enabled = self.redis.hget('machine_prefs', 'scanner_enabled') == "True" and _scanner_available
        if self.scanner_enabled:
            self.scanner = scanner2.Scanner(self.status, render_target=self.scanner_common_camera_image)

        # Scanner Scan DROs
        self.scanner_scan_dro_list = (
            'scanner_scan_x_start_dro',
            'scanner_scan_x_end_dro',
            'scanner_scan_y_start_dro',
            'scanner_scan_y_end_dro')

        scanner_dro_font_description  = pango.FontDescription('helvetica ultra-condensed 22')
        self.scanner_scan_dro_list = dict(((i, self.builder.get_object(i))) for i in self.scanner_scan_dro_list)
        for name, dro in self.scanner_scan_dro_list.iteritems():
            dro.modify_font(scanner_dro_font_description)


        if self.scanner:
            #KLUDGE scanner specific stuff should only happen if scanner is enabled?
            self.scanner.set_render_target(self.scanner_common_camera_image)

        ##############################################################
        # Initialize scanner DRO's
        # TODO: move to separate init function, pass in list of DRO's?

        self.scanner_brightness_adjustment = self.builder.get_object("scanner_brightness_adjustment")
        self.scanner_brightness_scale = self.builder.get_object("scanner_brightness_scale")
        self.scanner_brightness_scale.connect("scroll-event", self.on_mouse_wheel_event)
        self.scanner_brightness_adj_label = self.builder.get_object("scanner_brightness_adj_label")
        self.scanner_brightness_adjustment.set_value(50)

        self.scanner_contrast_adjustment = self.builder.get_object("scanner_contrast_adjustment")
        self.scanner_contrast_scale = self.builder.get_object("scanner_contrast_scale")
        self.scanner_contrast_scale.connect("scroll-event", self.on_mouse_wheel_event)
        self.scanner_contrast_adj_label = self.builder.get_object("scanner_contrast_adj_label")
        self.scanner_contrast_adjustment.set_value(50)

        self.scanner_scope_circle_dia_adjustment = self.builder.get_object("scanner_scope_circle_dia_adjustment")
        self.scanner_scope_circle_dia_scale = self.builder.get_object("scanner_scope_circle_dia_scale")
        self.scanner_scope_circle_dia_scale.connect("scroll-event", self.on_mouse_wheel_event)
        self.scanner_scope_circle_dia_adj_label = self.builder.get_object("scanner_scope_circle_dia_adj_label")
        self.scanner_scope_circle_dia_adjustment.set_value(30)

        self.scanner_status_textview = self.builder.get_object('scanner_status_textview')
        self.scanner_status_textbuffer = self.scanner_status_textview.get_buffer()
        self.scanner_status_textbuffer.set_text("Camera Status")

        self.scanner_common_working_fov_adjustment = self.builder.get_object('scanner_common_working_fov_adjustment')
        self.scanner_common_working_fov_hscrollbar = self.builder.get_object('scanner_common_working_fov_hscrollbar')
        self.scanner_common_working_fov_hscrollbar.connect("scroll-event", self.on_mouse_wheel_event)
        self.scanner_common_working_fov_adj_label = self.builder.get_object("scanner_common_working_fov_adj_label")
        self.scanner_common_working_fov_adjustment.set_value(70)
        self.scanner_common_working_fov_adj_label.set_text('70%')

        self.scanner_calibration_p1_text = self.builder.get_object('scanner_calibration_p1_text')
        self.scanner_calibration_p2_text = self.builder.get_object('scanner_calibration_p2_text')

        self.scanner_calibration_scale_text = self.builder.get_object('scanner_calibration_scale_text')

        # Define update function to poll camera and capture frames at slightly
        # faster than 30Hz to prevent frames from buffering up
        gobject.timeout_add(65, self.scanner_periodic)

    def scope_gui_init(self):
        """ Initialize objects in scanner scope tab of camera notebook"""

        # -----------------------------------------
        # scope table init (gtk.treeview)
        # -----------------------------------------
        self.scanner_scope_fixed = self.builder.get_object("scanner_scope_fixed")
        scope_font = pango.FontDescription('helvetica ultra-condensed 22')
        scope_i_font = pango.FontDescription('helvetica ultra-condensed 18')
        self.scope_row = 0

        self.scope_liststore = gtk.ListStore(str, str, str)

        for id_cnt  in range(1, self.DRILL_TABLE_ROWS + 1):
            self.scope_liststore.append([id_cnt, '', ''])

        self.scope_treeview = gtk.TreeView(self.scope_liststore)

        self.scope_i_column  = gtk.TreeViewColumn()
        self.scope_x_column  = gtk.TreeViewColumn('')
        self.scope_y_column  = gtk.TreeViewColumn('')

        self.scope_treeview.append_column(self.scope_i_column)
        self.scope_treeview.append_column(self.scope_x_column)
        self.scope_treeview.append_column(self.scope_y_column)

        self.scope_treeview.set_rules_hint(True)
        self.scope_treeview.set_headers_visible(False)
        self.scope_treeview.set_grid_lines(gtk.TREE_VIEW_GRID_LINES_BOTH)

        scope_i_renderer = gtk.CellRendererText()
        scope_i_renderer.set_property('editable', False)
        scope_i_renderer.set_property('cell-background', '#EEBBBB')
        scope_i_renderer.set_property('font-desc', scope_i_font)
        scope_i_renderer.set_property('xalign',0.5);
        self.scope_i_column.set_sizing(gtk.TREE_VIEW_COLUMN_FIXED)
        self.scope_i_column.set_fixed_width(30)
        self.scope_i_column.pack_start(scope_i_renderer, True)
        self.scope_i_column.set_attributes(scope_i_renderer, text=0)

        scope_x_renderer = gtk.CellRendererText()
        scope_x_renderer.set_property('editable', True)
        scope_x_renderer.set_property('font-desc', scope_font)
        scope_x_renderer.set_property('xalign',0.8);
        self.scope_x_column.set_sizing(gtk.TREE_VIEW_COLUMN_FIXED)
        self.scope_x_column.set_fixed_width(105)
        self.scope_x_column.pack_start(scope_x_renderer, True)
        self.scope_x_column.set_attributes(scope_x_renderer, text=1)
        scope_x_renderer.connect('edited', self.on_scope_x_column_edited, self.scope_liststore)

        scope_y_renderer = gtk.CellRendererText()
        scope_y_renderer.set_property('editable', True)
        scope_y_renderer.set_property('font-desc', scope_font)
        scope_y_renderer.set_property('xalign',0.8);
        self.scope_y_column.set_sizing(gtk.TREE_VIEW_COLUMN_FIXED)
        self.scope_y_column.set_fixed_width(105)
        self.scope_y_column.pack_start(scope_y_renderer, True)
        self.scope_y_column.set_attributes(scope_y_renderer, text=2)
        scope_y_renderer.connect('edited', self.on_scope_y_column_edited, self.scope_liststore)

        #scope_x_renderer.connect('editing-started', self.on_scope_x_column_editing_started, scope_font)
        #scope_y_renderer.connect('editing-started', self.on_scope_y_column_editing_started, scope_font)
        self.scope_x_renderer = scope_x_renderer
        self.scope_y_renderer = scope_y_renderer

        # show in notebook

        # create a scrolled window to hold the treeview
        self.scrolled_window_scope_table = gtk.ScrolledWindow()
        self.scrolled_window_scope_table.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        self.scanner_scope_fixed.put(self.scrolled_window_scope_table, 10, 120)
        self.scrolled_window_scope_table.add_with_viewport(self.scope_treeview)
        self.scrolled_window_scope_table.set_size_request(270, 200)


    # callbacks
    def get_linear_scale(self):
        """Return the scale factor for all linear axes based on current G20/G21 mode"""
        return 25.4 if self.g21 else 1.0

    def get_axis_scale(self, axis_ind):
        return self.get_linear_scale() if axis_ind < 3 else 1.0

    def setup_font_selector(self):
        """ Create font selector for conversational engraving"""
        num_fonts = 0
        if not is_ttlib:  # do we have font utilities?
            #print "--kw setup_font_selector error, no ttlib"
            return num_fonts
        if not os.path.isdir(ENGRAVING_FONTS_DIR):  # do we have a font directory?
            #print "--kw setup_font_selector error, no font dir"
            return num_fonts
        #print "--kw setup_font_selector, ttflib and font dir okay"

        self.font_file_list = []
        ef_name = ''
        ef_family = ''

        for engrave_font_file in os.listdir(ENGRAVING_FONTS_DIR):  # presort
            self.font_file_list.append(engrave_font_file)

        self.font_file_list = sorted(self.font_file_list)

        self.engrave_font_liststore = gtk.ListStore(str, str)  # file name, (name, family)

        for engrave_font_file in self.font_file_list:  # validate and build liststore
            try:
                (ef_name, ef_family) = self.get_ttfont_name(ENGRAVING_FONTS_DIR + engrave_font_file)
                #print "--kw font name, fam", ef_name, ef_family
            except:
                #print "--kw no font name found"
                pass
            if ef_name and ef_family:
                self.engrave_font_liststore.append([
                    ('<span weight="light" font_desc="helvetica ultra-condensed 16">%s</span>' %
                     engrave_font_file),
                    ('<span font_family="%s" font_desc="%s 20" foreground="blue">AaBb123</span>' %
                     (ef_family, ef_name))])

        try:
            # generates exception if TreeView not yet created
            # no need for full TreeView initialization
            # only need to set the new model
            self.engrave_font_treeview.set_model(self.engrave_font_liststore)

        except AttributeError:
            # first time through will get this exception for TreeView.set_model()
            self.engrave_font_treeview = gtk.TreeView(self.engrave_font_liststore)
            font_column_renderer = gtk.CellRendererText()
            font_column = gtk.TreeViewColumn('Font', font_column_renderer, markup=0)
            self.engrave_font_treeview.append_column(font_column)

            sample_column_renderer = gtk.CellRendererText()
            sample_column =  gtk.TreeViewColumn('Sample', sample_column_renderer, markup=1)
            self.engrave_font_treeview.append_column(sample_column)

            self.engrave_font_treeview.set_headers_visible(False)

            self.scrolled_window_engrave_font = gtk.ScrolledWindow()
            self.scrolled_window_engrave_font.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

            self.conv_engrave_fixed.put(self.scrolled_window_engrave_font, 55, 50)
            self.scrolled_window_engrave_font.add_with_viewport(self.engrave_font_treeview)
            self.scrolled_window_engrave_font.set_size_request(450, 140)

            # events to handle
            ##self.engrave_font_treeview.connect("button_press_event", self.on_engrave_font_tview_click)  # only updates sample label
            self.engrave_font_treeview.connect("cursor_changed", self.on_engrave_font_tview_cursor_changed)  # centers active row, updates sample

            # set initial font to first entry in list
            self.engrave_font_row = 0

        tvselection = self.engrave_font_treeview.get_selection()
        tvselection.select_path(self.engrave_font_row)
        self.engrave_font_pf = os.path.join(ENGRAVING_FONTS_DIR, self.font_file_list[self.engrave_font_row])
        (ef_name, ef_family) = self.get_ttfont_name(self.engrave_font_pf)

        engrave_text = self.engrave_dro_list['engrave_text_dro'].get_text()
        # draw sample text in selected font
        self.engrave_sample_update()

        ef_num_rows = len(self.engrave_font_liststore)
        return ef_num_rows

    # button press event for all widgets simply moves the eventbox to simulate a 'regular' gtk button motion
    def on_button_press_event(self, widget, data=None):

        # gtk.buildable.get_name returns glade object names
        # wigdet.get_name gets imagebutton names
        name = gtk.Buildable.get_name(widget) or widget.get_name()
        msg = name + " button was pressed at " + datetime.datetime.now().strftime(" %Y-%m-%d %H:%M:%S")

        self.error_handler.write(msg, ALARM_LEVEL_DEBUG)
        do_button_press_motion(widget)

    def is_number(self, text):
        try:
            val = float(text)
            return (True, val)
        except ValueError:
            return(False, 0)

    def on_spindle_hispeed_min_entry_activate(self, widget, data=None):
        (is_valid, value) = self.is_number(widget.get_text())
        if (not is_valid):
            # clear entry
            widget.set_text('%d' % self.spindle_hispeed_min)
        else:
            self.spindle_hispeed_min = abs(value)
            widget.set_text('%d' % self.spindle_hispeed_min)

        self.hal['spindle-hispeed-min'] = self.spindle_hispeed_min
        self.redis.hset('machine_prefs', 'spindle_hispeed_min', '%d' % self.spindle_hispeed_min);
        self.window.set_focus(None)

    def on_spindle_hispeed_max_entry_activate(self, widget, data=None):
        (is_valid, value) = self.is_number(widget.get_text())
        if (not is_valid):
            # clear entry
            widget.set_text('%d' % self.spindle_hispeed_max)
        else:
            self.spindle_hispeed_max = abs(value)
            widget.set_text('%d' % self.spindle_hispeed_max)

        self.hal['spindle-hispeed-max'] = self.spindle_hispeed_max
        self.redis.hset('machine_prefs', 'spindle_hispeed_max', '%d' % self.spindle_hispeed_max);
        self.window.set_focus(None)

    def on_spindle_type_combobox_changed(self, widget, data=None):
        #spindle_text = widget.get_active_text()
        #print spindle_text
        spindle_type = widget.get_active()
        self.spindle_type = spindle_type
        self.hal['spindle-type'] = self.spindle_type
        # make persistent
        self.redis.hset('machine_prefs', 'spindle_type', '%d' % self.spindle_type);
        self.make_hispeed_min_max_visible(self.spindle_type)

        if (spindle_type == SPINDLE_TYPE_HISPEED and self.checkbutton_list['use_atc_checkbutton'].get_active()):
            self.checkbutton_list['use_manual_toolchange_checkbutton'].set_active(True)
            self.error_handler.write('Cannot use high speed spindle and ATC. Disabling ATC.')

    # edit selected or else currently loaded gcode file
    def on_edit_gcode_button_release_event(self, widget, data=None):
        # WHAT IS THE PURPOSE OF THIS SLEEP !?!?!?!?!?
        time.sleep(0.3)
        # the usually checking of button permissions with if self.check_button_permissions(widget): return
        # does not do what we want for Edit G-code which should be available any time except
        # while a program is running and before RESET has been pressed
        if self.moving():
            return
        path = self.hd_file_chooser.selected_path
        if path:
            print "Editing file on HD:", path
        if path == '':
            path = self.usb_file_chooser.selected_path
            print "Editing file on USB:", path
        if path == '':
            path = self.current_gcode_file_path
            print "Editing loaded G code file:", path
        # path can be blank if no file loaded
        self.edit_gcode_file(path)


    def edit_gcode_file(self, path):
        file_name_for_display = path.replace(GCODE_BASE_PATH + '/', '')
        self.error_handler.write('Editing G code file: %s' % file_name_for_display, ALARM_LEVEL_DEBUG)
        try:
            # run the editor, store the pid somewhere in case of crash
            self.editor_pid = subprocess.Popen([self.gcode_edit_program_to_run, path]).pid
        except OSError:
            self.error_handler.write("OSError exception raised. Could not run edit program: %s" % self.gcode_edit_program_to_run, ALARM_LEVEL_LOW)
        except IOError:
            print "path %s is not a valid G code file" % path


    # this has to create then append our menu item then call show()
    def on_gcode_sourceview_populate_popup(self, textview, menu):
        set_start_line_item = gtk.MenuItem("Set start line")
        set_start_line_item.connect("activate", self.set_start_line_callback)
        # get rid of all default gtk.sourceview menu options
        for child in menu.get_children():
            menu.remove(child)
        menu.append(set_start_line_item)
        set_start_line_item.show()


    def set_start_line_callback(self, widget):
        self.set_start_line()

    def on_filechooserwidget_file_activated(self, widget, data=None):
        self.gcode_filename = os.path.join(self.directory, widget.get_filename())
        self.load_gcode_file()


    def on_gcode_filechooserbutton_file_set(self, widget):
        self.gcode_filename = os.path.join(self.directory, widget.get_filename())
        self.load_gcode_file()

    def load_gcode_file(self, path):
        self.elapsed_time_label.set_text('')
        if self.moving():
            if self.feedhold_active.is_set():
                self.error_handler.write("Machine is in feedhold - press stop or reset to clear feedhold before loading a g code program")
                return
            self.error_handler.write("Cannot load a g code program while machine is moving.")
            return
        self.is_gcode_program_loaded = True
        # remember what was last loaded to watch for changes on disk and reload
        self.set_current_gcode_path(path)
        if not path:
            self.gcodelisting_buffer.set_text('')
            return

        # prevent changes to the combo box from causing file loads
        self.combobox_masked = True
        # remove filename from previous model position if it was previously in the model
        sort_file_history(self.file_history_liststore, path)
        # if the model is longer than xxx files, remove the last one

        # add filename, path to the model
        self.file_history_liststore.prepend([os.path.basename(path), path])

        # have to set active one, else the active file won't be displayed on the combobox
        self.loaded_gcode_filename_combobox.set_active(0)

        # unmask
        self.combobox_masked = False

        # read file directly into buffer
        tormach_file_util.open_text_file(self, path, self.gcodelisting_buffer)

        # can change this with right-click menu in source view
        # this is one based, the textbuffer is zero based
        self.gcode_start_line = 1;
        # must switch to mdi, then back to force clear of _setup.file_pointer, otherwise
        # we can't open a program if one is already open
        self.ensure_mode(linuxcnc.MODE_MDI)
        # load file into LinuxCNC
        self.ensure_mode(linuxcnc.MODE_AUTO)
        self.command.program_open(path)
        # note the time stamp
        self.gcode_file_mtime = os.stat(path).st_mtime

        # gremlin is unpredictable at the moment
        # wrap it for exceptions
        try:
            self.gremlin.clear_live_plotter()
        except Exception as e:
            print 'gremlin.clear_live_plotter() raised an exception'
            msg = "An exception of type {0} occured, these were the arguments:\n{1!r}"
            print msg.format(type(e).__name__, e.args)
            #traceback_txt = "".join(traceback.format_exception(*sys.exc_info()))
            #print traceback_txt

        try:
            # with no filename given, gremlin will ask LinuxCNC for the filename
            result, seq, warnings = self.gremlin.load()
            #Quick way to dump warnings to status window
            self.gremlin.report_gcode_warnings(warnings,os.path.basename(path))

        except Exception as e:
            print 'gremlin.load() raised an exception'
            msg = "An exception of type {0} occured, these were the arguments:\n{1!r}"
            print msg.format(type(e).__name__, e.args)
            #traceback_txt = "".join(traceback.format_exception(*sys.exc_info()))
            #print traceback_txt

        try:
            self.gremlin.set_highlight_line(None)
        except Exception as e:
            print 'gremlin.set_highlight_line() raised an exception'
            msg = "An exception of type {0} occured, these were the arguments:\n{1!r}"
            print msg.format(type(e).__name__, e.args)
            #traceback_txt = "".join(traceback.format_exception(*sys.exc_info()))
            #print traceback_txt

        try:
            self.gremlin.set_view_z()
        except Exception as e:
            print 'gremlin.set_y_view() raised an exception'
            msg = "An exception of type {0} occured, these were the arguments:\n{1!r}"
            print msg.format(type(e).__name__, e.args)
            #traceback_txt = "".join(traceback.format_exception(*sys.exc_info()))
            #print traceback_txt

        # switch to gcode listing MDI main tab
        if not self.interp_alarm:
            self.notebook.set_current_page(self.notebook.page_num(self.notebook_main_fixed))
        self.window.set_focus(None)
        self.gcodelisting_mark_start_line()
        self.gcode_pattern_search.on_load_gcode()


    def on_gcode_scrollbar_button_press(self, vscrollbar, event, data=None):
        # mask the motion line update so user can scroll through code without periodic update stepping on his scrolling
        self.sourceview.masked = True

    def on_gcode_scrollbar_button_release(self, scroll_window, event, data=None):
        self.sourceview.masked = False


    # MDI line


    def on_mdi_line_changed(self, widget, data=None):
        # catch all typing, convert to uppercase
        widget.set_text(widget.get_text().upper())


    def on_mdi_line_gets_focus(self, widget, event):
        # prevent access to MDI line when running a program.
        if self.moving():
            self.window.set_focus(None)
            return True
        if not widget.has_focus():
            self.mdi_line.set_text('')
        self.mdi_line.modify_text(gtk.STATE_NORMAL, gtk.gdk.Color('black'))
        self.mdi_line.modify_base(gtk.STATE_NORMAL, gtk.gdk.Color(HIGHLIGHT))
        self.mdi_line_masked = 1
        if self.touchscreen_enabled:
            numpad.numpad_popup(widget, True)
            self.mdi_line_masked = 0
            self.window.set_focus(None)
            return True


    def on_mdi_line_loses_focus(self, widget, event):
        self.mdi_line.modify_base(gtk.STATE_NORMAL, gtk.gdk.Color('white'))
        self.mdi_line.modify_text(gtk.STATE_NORMAL, gtk.gdk.Color('#C3C9CA'))
        self.mdi_line.set_text('MDI')
        self.mdi_line.select_region(0, 0)
        if not self.touchscreen_enabled:
            self.mdi_line_masked = 0
        return False
        #Don't want to emulate this Mach3 behavior
        #if self.moving() and not self.program_running():
            #self.stop_motion_safely()

    def on_mdi_line_key_press_event(self, widget, event):
        if event.keyval == gtk.keysyms.Escape:
            self.window.set_focus(None)
            if self.touchscreen_enabled:
                self.on_mdi_line_loses_focus(self, widget)
            return True

        if event.keyval == gtk.keysyms.Return:
            if self.gcode_pattern_search.find_last(event):
                return True

        if event.keyval == gtk.keysyms.Down:
#           if self.gcode_pattern_search.mdi_key_command(event):
#               return True
            # range check history index
            self.mdi_history_index -= 1
            if self.mdi_history_index < -1:
                self.mdi_history_index = -1
            if self.mdi_history_index >= 0:
                history_len = len(self.mdi_history)
                if history_len > 0:
                    # place historic text in the display
                    self.mdi_line.set_text(self.mdi_history[self.mdi_history_index])
                    # place cursor at end of line
                    self.mdi_line.set_position(-1)
            else:
                self.mdi_line.set_text("")
            # indicate key has been processed
            return True
        elif event.keyval == gtk.keysyms.Up:
#           if self.gcode_pattern_search.mdi_key_command(event):
#               return True
            self.mdi_history_index += 1
            # range check history index
            history_len = len(self.mdi_history)
            if self.mdi_history_index >= history_len:
                self.mdi_history_index = history_len - 1
            if history_len > 0:
                # place the historic text in the display
                self.mdi_line.set_text(self.mdi_history[self.mdi_history_index])
                # place cursor at end of line
                self.mdi_line.set_position(-1)
            # indicate key has been processed
            return True

        # indicate key not processed
        return False

    def on_mdi_line_activate(self, widget):
        self.mdi_history_index = -1
        command_text = self.mdi_line.get_text()
        # remove leading white space
        command_text = command_text.lstrip()
        # remove trailing white space
        command_text = command_text.rstrip()
        # ignore empty command text
        if len(command_text) == 0:
            # ignore empty command text
            return

        # insert into history
        self.mdi_history.insert(0, command_text)
        history_len = len(self.mdi_history)
        # limit number of history entries
        if history_len > self.mdi_history_max_entry_count:
            # remove oldest entry
            self.mdi_history.pop()
        # delete second occurance of this command if present
        try:
            second_occurance = self.mdi_history.index(command_text, 1)
            if second_occurance > 0:
                self.mdi_history.pop(second_occurance)
        except ValueError:
            # not a problem
            pass

        if (mdi_find_command(self, command_text)):
            return

        if (mdi_admin_commands(self, command_text)):
            return

        if not (self.x_referenced and self.y_referenced and self.z_referenced):
            self.error_handler.write("Must reference X, Y, and Z axes before issuing command: " + command_text, ALARM_LEVEL_MEDIUM)
            self.mdi_line.set_text("")
            self.window.set_focus(None)
            return

        #KLUDGE test for exclusive MDI access by other stuff (scanner, etc.)
        if self.scanner and self.scanner.moving():
            self.error_handler.write('Cannot execute an MDI motion during a scan')
            return

        # change to MODE_MDI and issue command
        '''if 'M6' in command_text:
            self.command.reset_interpreter()
            if self.is_gcode_program_loaded:
                # put back the part program after reset
                self.load_gcode_file(self.current_gcode_file_path)'''

        # do the command
        self.issue_mdi(command_text)

        # clear the text on the input line
        self.mdi_line.set_text("")

        if self.touchscreen_enabled:
            # we don't want the blue highlight to remain
            self.window.set_focus(None)
            self.on_mdi_line_loses_focus(self, widget)

        # look for an M30 in the string
        # it could be inside a comment but who would type a comment into an MDI line?
        if 'M30' in command_text:
            # reset starting line
            self.gcodelisting_mark_start_line(1)

    # ---------------------------------------
    # Program Control Group
    # ---------------------------------------

    def on_cycle_start_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        #KLUDGE check for scanner running
        #TODO refactor this to handle pre-conditions more consistently
        if self.scanner and self.scanner.moving():
            if self.feedhold_active.is_set():
                self.feedhold_active.clear()
                return
            else:
                self.error_handler.write('Cannot start program during a scan')
                return
        if self.status.axis[0]['homing'] or self.status.axis[1]['homing'] or self.status.axis[2]['homing']:
            self.error_handler.write('Cannot start program while machine is referencing')
            return

        if self.door_sw_status:
            self.error_handler.write("Must close enclosure door before starting program", ALARM_LEVEL_LOW)
            return

        # cycle start after text line message in Gremlin
        # order of these is important.  Answer queries first, then check for random stop/reset presses
        self.clear_message_line_text() # Alwsays do this in case of left over crap
        if self.notify_at_cycle_start:  # is anyone waiting on us
            self.notify_at_cycle_start = False
            try:
                self.redis.hset("TormachAnswers",self.notify_answer_key,"Y")  #start pressed message
                self.hal['prompt-reply'] = 1
                print ("prompt output pin set to 1 by cycle start")
            except Exception as e:
                print "Whooops! - Tormach message reply not set", e

            return  #wake up process waitin on  message answer

        if self.atc.feed_hold.isSet() :             #we are only resuming a change operation now
            self.atc.feed_hold.clear()  # if it's set , clear it now
            self.set_image('feedhold_image', 'Feedhold-Black.jpg')
            if self.status.paused:   #start up operation even if on ATC page
                if self.single_block_active:
                    # Hack to fix "queueing" behavior where pushing cycle start
                    # multiple times steps through multiple segments
                    if self.status.current_vel < 1e-9:
                        self.command.auto(linuxcnc.AUTO_STEP)
                else:
                    self.command.auto(linuxcnc.AUTO_RESUME)
                    return
            return   #continue changing



        if self.notebook.get_current_page() != MAIN_PAGE:
            self.error_handler.write("Cannot start program while not on Main screen", ALARM_LEVEL_LOW)
            return

        if not (self.x_referenced and self.y_referenced and self.z_referenced):
            self.error_handler.write("Must reference X, Y, and Z axes before executing a gcode program", ALARM_LEVEL_MEDIUM)
            return

        if self.program_paused_for_door_sw_open:
            self.error_handler.write("Resuming program because door sw was closed", ALARM_LEVEL_DEBUG)
            self.program_paused_for_door_sw_open = False
            # iocontrol.coolant is checked in the 50ms periodic.  If it doesn't match the previous state,
            # we flip the hal.coolant bit accordingly.  This next line will force this to happen
            self.prev_coolant_iocontrol = not self.hal['coolant-iocontrol']

        # pressing CS should always clear feedhold.
        self.feedhold_active.clear()
        self.set_image('feedhold_image', 'Feedhold-Black.jpg')

        # An image from `M01 (myimg.jpg)` would be hidden after a
        # state change, but detecting that can take a half second
        self.hide_m1_image()

        # make sure we aren't walking and chewing gum at same time. Cycle start can sneak in between
        # process queue thread requests. Any problems clearing the tray require human intervention.
        # Also, we need to make sure we aren't just cycle starting a halted M6 remap here.

        if self.atc.operational and (not self.hal['atc-ngc-running']):   #now check the tray
            r = self.atc.cycle_start ()
            if r == 'queue active' :
                self.error_handler.write('ATC - Wait until action in process completes, then try again', ALARM_LEVEL_MEDIUM)
                return
            if r == 'tray in' :  #returned with problem clearing tool tray automatically
                self.error_handler.write('ATC - Retract tool tray before cycle start', ALARM_LEVEL_MEDIUM)
                self.command.auto(linuxcnc.AUTO_PAUSE)

        if not self.is_gcode_program_loaded and not self.moving():
            self.error_handler.write("No G Code program loaded.", ALARM_LEVEL_MEDIUM)

        # if status.paused, we're already in MODE_AUTO, so resume the program
        if self.status.paused:
            if self.single_block_active:
                self.command.auto(linuxcnc.AUTO_STEP)
            else:
                self.command.auto(linuxcnc.AUTO_RESUME)
                return
        self.gcode_pattern_search.clear()
        # Otherwise, switch to MODE_AUTO and run the code
        if self.status.interp_state == linuxcnc.INTERP_IDLE:
            self.ensure_mode(linuxcnc.MODE_AUTO)
            if self.single_block_active:
                #Starting for the first time in single block mode
                #Takes 3 steps to execute the first line
                if self.gcode_start_line != 1:
                    self.command.auto(linuxcnc.AUTO_RUN, self.gcode_start_line -1)
                    self.command.auto(linuxcnc.AUTO_PAUSE)
                    self.command.auto(linuxcnc.AUTO_STEP)
                    self.set_start_line(1)
                else:
                    self.command.auto(linuxcnc.AUTO_STEP)
            else:
                self.command.auto(linuxcnc.AUTO_RUN, self.gcode_start_line -1)
                self.set_start_line(1)


    def on_single_block_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # unconditionally set sb_active flag and button image
        if self.single_block_active:
            self.single_block_active = False
            self.set_image('single_block_image', 'Single-Block-Black.jpg')
        else:
            self.single_block_active = True
            self.set_image('single_block_image', 'Single-Block-Green.jpg')

        # if machine is in feedhold, do notihing (SB button press should not cause machine to come out of feedhold)
        if self.feedhold_active.is_set(): return
        if self.command_in_progress():
            if not self.single_block_active:
                # only do the auto_resume if we're already in the middle of a move!
                if self.status.current_vel != 0:
                    self.command.auto(linuxcnc.AUTO_RESUME)
            else:
                self.command.auto(linuxcnc.AUTO_PAUSE)
                self.command.auto(linuxcnc.AUTO_STEP)



    def on_m01_break_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        if  self.m01_break_active:
            self.command.set_optional_stop(False)
            self.m01_break_active = False
            self.set_image('m01_break_image', 'M01-Break-Black.jpg')
        else:
            self.command.set_optional_stop(True)
            self.m01_break_active = True
            self.set_image('m01_break_image', 'M01-Break-Green.jpg')

    def on_feedhold_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # should have no effect when the machine isn't moving, except in middle of atc cycle
        if self.atc.in_a_thread.isSet() :  #if a thread is running, hold on til cycle start
            self.atc.feed_hold.set()
            self.command.auto(linuxcnc.AUTO_PAUSE)
            self.set_image('feedhold_image', 'Feedhold-Green.jpg')
        #KLUDGE set feedhold active so that the scanner thread knows
        if self.scanner and self.scanner.moving():
            self.feedhold_active.set()
        if not self.moving(): return
        if not self.feedhold_active.is_set():
            self.command.auto(linuxcnc.AUTO_PAUSE)
            self.feedhold_active.set()
            self.set_image('feedhold_image', 'Feedhold-Green.jpg')

    def on_stop_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.clear_message_line_text()
        self.set_response_cancel ()  #check for outstanding user prompts and cancel
        self.stop_motion_safely()
        if self.scanner is not None:
            self.scanner.stop_threads()

    def stop_motion_safely(self):

        #Send abort message to motion to stop any movement
        self.command.abort()

        #self.command.wait_complete()

        if self.atc.in_a_thread.isSet() :
            self.atc.stop_reset.set()   #only if atc thread in progress
        if self.atc.operational and self.hal['atc-device-status']:  #gotta kill blaster no matter what
            self.atc.blast_off()
        self.hardkill_coolant = True  #can the spray
        self.coolant_ticker = 0
        if self.feedhold_active.is_set():
            self.feedhold_active.clear()
            #TODO move this to status update
            self.set_image('feedhold_image', 'Feedhold-Black.jpg')
        if self.is_gcode_program_loaded: self.gcodelisting_mark_motion_line(0)


    def on_coolant_button_release_event(self, widget, data=None):
        # POSTGUI_HALFILE contains:
        # net coolant-flood tormach.coolant => parport.0.pin-14-out
        # net coolant-flood-io iocontrol.0.coolant-flood => tormach.coolant-iocontrol
        # The UI code here watches tormach.coolant-iocontrol for changes from LinuxCNC.
        # See the periodic handler for details
        if not self.check_button_permissions(widget): return
        # use our tormach.coolant HAL pin to track actual coolant state
        # only toggle flood on and off if mist isn't on
        # but turn off mist if on, mist must turn on only with M7

        if  not self.hal['mist']:
            self.hal['coolant'] = not self.hal['coolant']
        if self.hal['mist']:
            self.hal['mist']= self.hal['coolant'] = False

    def on_reset_button_release_event(self, widget, data=None):


        if not self.check_button_permissions(widget): return
        self.clear_message_line_text()

        # order of these is important.  Answer queries first, then check for random stop/reset presses
        if self.set_response_cancel(): return        #check for outstanding prompts and cancel,True is message answered

        if self.atc.in_a_thread.isSet() :
            self.atc.stop_reset.set()   #only if atc thread in progress
            self.atc.feed_hold.clear()  # clear any feed holds
            self.set_image('feedhold_image', 'Feedhold-Black.jpg')

        if self.feedhold_active.is_set():
            self.feedhold_active.clear()
            self.set_image('feedhold_image', 'Feedhold-Black.jpg')
        # clear Mesa card watchdog
        self.hal['mesa-watchdog-has-bit'] = 0
        self.mesa_watchdog_has_bit_seen = False
        # clear alarm
        self.estop_alarm = False
        self.display_estop_msg = True
        #self.error_handler.clear()

        # reset e-stop
        if self.status.task_state != linuxcnc.STATE_ESTOP_RESET:
            self.command.state(linuxcnc.STATE_ESTOP_RESET)
            # leave this wait_complete() in place, see issue #264
            self.command.wait_complete()
        #Check if we've actually turned on
        self.status.poll()
        if self.status.task_state != linuxcnc.STATE_ESTOP_RESET and self.status.task_state != linuxcnc.STATE_ON :
            self.error_handler.write("Failed to bring machine out of E-stop. Please check machine power or DB-25 communication cable from the controller to the machine.")
            return
        # apparently must be turned on again after being reset from estop
        if self.status.task_state != linuxcnc.STATE_ON:
            self.command.state(linuxcnc.STATE_ON)
            self.command.wait_complete()

        # stop motion
        self.command.abort()

        # suppress coolant action for full second
        self.hardkill_coolant = True
        self.coolant_ticker = 0

        # reset/rewind program
        if (self.status.limit[0] == 0) and (self.status.limit[1] == 0) and (self.status.limit[2] == 0):
            self.issue_mdi('M30')
        # clear SB status
        self.single_block_active = False
        self.set_image('single_block_image', 'Single-Block-Black.jpg')
        # clear live plotter
        self.gremlin.clear_live_plotter()
        # refresh work offsets
        self.refresh_work_offset_liststore()
        # rewind program listing and set starting line
        if self.is_gcode_program_loaded:
            self.gcodelisting_mark_start_line(1)
            self.sourceview.scroll_to_mark(self.gcodelisting_start_mark, 0, True, 0, 0.5)


        self.do_first_run_setup()


    def do_first_run_setup(self):

        if not self.first_run:
            return


        self.first_run = False
        #purge any left over message and answersfrom prior aborts in redis queue
        try:
            self.redis.delete('TormachMessage')
            self.redis.delete('TormachAnswers')
        except:
            pass

        # custom X/Y soft limits

        self.status.poll()
        self.ensure_mode(linuxcnc.MODE_MANUAL)

        #For some bizarre reason, changing to mode manual turns on mist pins
        #Just overlay the input pin it networked to with a False to cancel the wierdness
        self.hal["mist-iocontrol"] = False


        try:
            self.x_soft_limit = float(self.redis.hget('machine_prefs', 'x_soft_limit'))
            print 'setting X soft limit to: %f' % self.x_soft_limit
            self.command.set_max_limit(0, self.x_soft_limit)
        except Exception as e:
            print 'exception getting X soft limit from redis - not setting'
            #msg = "An exception of type {0} occured, these were the arguments:\n{1!r}"
            #print msg.format(type(e).__name__, e.args)

        try:
            self.y_soft_limit = float(self.redis.hget('machine_prefs', 'y_soft_limit'))
            print 'setting Y soft limit to: %f' % self.y_soft_limit
            self.command.set_min_limit(1, self.y_soft_limit)
        except Exception as e:
            print 'exception getting Y soft limit from redis - not setting'
            #msg = "An exception of type {0} occured, these were the arguments:\n{1!r}"
            #print msg.format(type(e).__name__, e.args)



        try:
            self.z_soft_limit = float(self.redis.hget('machine_prefs', 'z_soft_limit'))
            print 'setting Z soft limit to: %f' % self.z_soft_limit
            self.command.set_min_limit(2, self.z_soft_limit)
        except Exception as e:
            print 'exception getting Z soft limit from redis - not setting'
            #msg = "An exception of type {0} occured, these were the arguments:\n{1!r}"
            #print msg.format(type(e).__name__, e.args)


        self.status.poll()
        self.ensure_mode(linuxcnc.MODE_MDI)
        try:
            if self.redis.hget('machine_prefs', 'g21') == "True":
                self.issue_mdi("G21")
                # need wait_complete or else subsequent tool change will fail
                self.command.wait_complete()

            # RESET TOOL IN SPINDLE WITH M61 TO BYPASS TOOL CHANGING
            tool_num = self.redis.hget('machine_prefs', 'active_tool')
            if int(tool_num) < 0 : tool_num = '0'
            self.issue_mdi("M61 Q" + tool_num)
            self.command.wait_complete()
            self.issue_mdi('G43')

            feedrate = self.redis.hget('machine_prefs', 'feedrate')
            print "feedrate: ", feedrate
            if feedrate != '0' and feedrate != None:
                g94_command = "G94 F%.4f" % float(feedrate)
                self.issue_mdi(g94_command)

            spind_speed = self.redis.hget('machine_prefs', 'spindle_speed')
            if spind_speed != '0' and spind_speed != None:
                s_command = "S%.4f" % float(spind_speed)
                self.issue_mdi(s_command)

            #reference Z for tool changer
            '''
            if self.atc.operational:
                self.atc.hey_hal(ATC_QUERY_SENSOR,ATC_TRAY_IN_SENSOR)  #wake it up , sensor update
                if self.hal ["atc-hal-return"] >= 0 :    #don't try anything if ATC not working
                    dialog = tormach_file_util.ok_cancel_popup('Reference     Z       axis     now?');
                    dialog.run();
                    response = dialog.response;
                    dialog.destroy()
                    if response == gtk.RESPONSE_OK :
                        self.atc.ref_z ()
            '''

        except Exception as e:
            print "Redis failed to retrieve tool information!", e
            pass



    def on_feedrate_override_adjustment_value_changed(self, adjustment):
        # important to not display 0% when value is > 0.0 and < 1.0
        percentage = adjustment.value
        if percentage > 0.0 and percentage < 1.0:
            percentage = 1.0
        self.feedrate_override_label.set_text(str(int(percentage))+"%")
        self.command.feedrate(adjustment.value / 100.0)

    def on_feedrate_override_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.feedrate_override_adjustment.set_value(100)

    def on_spindle_override_adjustment_value_changed(self, adjustment):
        self.spindle_override_label.set_text(str(int(adjustment.value))+"%")
        self.command.spindleoverride(adjustment.value / 100.0)

    def on_rpm_override_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.spindle_override_adjustment.set_value(100)

    def on_maxvel_override_adjustment_value_changed(self, adjustment):
        self.maxvel_override_label.set_text(str(int(adjustment.value))+"%")
        # scale this to a percentage of the traj setting
        scaled_val_lin = adjustment.value * self.maxvel_lin / 100
        scaled_val_ang = adjustment.value * self.maxvel_ang / 100
        self.command.maxvel(scaled_val_lin, scaled_val_ang)
        self.window.set_focus(None)

    def on_maxvel_override_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.maxvel_override_adjustment.set_value(100)

    # TODO: move below conversational and probing handler sections?
    # -------------------------------------------------------------------------------------------------
    # Scanner Handlers
    # -------------------------------------------------------------------------------------------------

    def on_camera_notebook_switch_page(self, notebook, page, page_num):
        #KLUDGE using numbers here
        if page_num == 0: #Calibration
            pass
        elif page_num == 1: #Scan
            #Ugly way to force all DRO's to update, spams output though
            #FIXME, long recalculation with lots of points
            self.on_scanner_scan_x_start_dro_activate(self.scanner_scan_dro_list['scanner_scan_x_start_dro'])
            self.on_scanner_scan_x_end_dro_activate(self.scanner_scan_dro_list['scanner_scan_x_end_dro'])
            self.on_scanner_scan_y_start_dro_activate(self.scanner_scan_dro_list['scanner_scan_y_start_dro'])
            self.on_scanner_scan_y_end_dro_activate(self.scanner_scan_dro_list['scanner_scan_y_end_dro'])
            try:
                self.scanner.camera.set_window_from_fov(self.scanner.scene.fov_ratio)
            except AttributeError:
                pass

    def on_scanner_common_working_fov_adjustment_value_changed(self, adjustment):
        fov_ratio = float(adjustment.value)/100.0
        try:
            self.scanner.scene.set_fov_ratio(fov_ratio)
            #FIXME fails on startup since camera doesn't exist at first. Maybe move this to a scene setting instead?
            self.scanner.scene.update_scanpoints(self.scanner.camera.get_frame_size())
            self.scanner_display_scanpoints()
        except AttributeError:
            pass
        #TODO simplify this conversion
        self.scanner_common_working_fov_adj_label.set_text(str(int(adjustment.value))+"%")

    def on_scanner_brightness_adjustment_value_changed(self, adjustment):
        self.scanner_brightness_adj_label.set_text(str(int(adjustment.value))+"%")

        brightness = adjustment.value / 100.0
        #TODO avoid redundant checks like this by controlling sensitivity on toggle
        if self.scanner and self.scanner.camera:
            self.scanner.camera.set_brightness(brightness)
        #os.system('v4l2-ctl --set-ctrl=brightness=%s' % brightness)

    def on_scanner_contrast_adjustment_value_changed(self, adjustment):
        self.scanner_contrast_adj_label.set_text(str(int(adjustment.value))+"%")
        contrast = adjustment.value / 100.0
        #os.system('v4l2-ctl --set-ctrl=contrast=%s' % contrast)
        if self.scanner and self.scanner.camera:
            self.scanner.camera.set_contrast(contrast)

    def on_scanner_scope_circle_dia_adjustment_value_changed(self, adjustment):
        #print "--kw scope circle dia =", adjustment.value
        self.scanner_scope_circle_dia_adj_label.set_text(str(int(adjustment.value))+"px")
        if self.scanner:
            self.scanner.scope_circle_dia = adjustment.value

    def on_scanner_camera_on_off_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return

        if self.scanner.camera is not None:
            self.set_image('scanner_camera_on_off_image', 'button_camera_off.png')
            self.scanner.remove_camera()
        else:
            if self.scanner.create_camera():
                self.set_image('scanner_camera_on_off_image', 'button_camera_on.png')
            else:
                self.set_image('scanner_camera_on_off_image', 'button_camera_off.png')

    def on_scanner_camera_snap_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.scanner.save_snapshot()
        print "saved snapshot"

    def on_scanner_scan_start_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        path = self.last_used_save_as_path + os.path.sep + ''
        if self.scanner and self.scanner.running():
            self.error_handler.write("Can't start a scan while already running as scan",ALARM_LEVEL_LOW)
            return
        with tormach_file_util.save_as_popup(path, self.touchscreen_enabled) as dialog:
            # Get information from dialog popup
            response = dialog.response
            path = dialog.path
            self.scanner.set_filename(path)
            self.last_used_save_as_path = dialog.current_directory

        if response != gtk.RESPONSE_OK:
            return
        #TODO validation of parameters in scanner
        #TODO better validation that GUI state has propagated to scanner
        self.scanner.use_inch = not self.g21
        self.scanner.start(self.feedhold_active)
        self.save_conv_parameters(self.scanner_scan_dro_list)

    def on_scanner_status_update_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        scanner_text_proc = subprocess.Popen(['v4l2-ctl --all'], stdout=subprocess.PIPE, shell=True)
        (stp_out, stp_err) = scanner_text_proc.communicate()
        scanner_menu_proc = subprocess.Popen(['v4l2-ctl --list-ctrls-menus'], stdout=subprocess.PIPE, shell=True)
        (smp_out, smp_err) = scanner_menu_proc.communicate()

        self.scanner_status_textbuffer.set_text('*** Camera Information\n' + stp_out + '\n*** Control Menu List\n' + smp_out)

    def on_scanner_calibration_complete(self):
        self.get_obj("scanner_calibration_complete_image").set_from_stock(gtk.STOCK_APPLY,gtk.ICON_SIZE_LARGE_TOOLBAR)
        self.get_obj("scanner_scan_start").set_sensitive(True)

    def on_scanner_calibration_set_p1_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # read and store machine position for P1
        xypos = self.get_local_position()[0:2]
        # If we got a scale factor, indicate to the user that calibration is
        # done
        if self.scanner.scene.set_first_point(xypos):
            self.on_scanner_calibration_complete()
        self.scanner_calibration_p1_text.set_markup('<span weight="light" font_desc="Bebas 12" font_stretch="ultracondensed" foreground="white" >P1    :    (   %s  ,  %s    )</span>' % (self.dro_long_format, self.dro_long_format) % tuple(xypos))
        self.scanner_calibration_scale_text.set_markup('<span weight="light" font_desc="Bebas 12" font_stretch="ultracondensed" foreground="white" >Scale   :   %s   ,   Angle  :  %s &#xB0;   </span>' % (self.dro_long_format, self.dro_long_format) % (self.scanner.scene.scale,self.scanner.scene.angle))

    def on_scanner_calibration_set_p2_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        xypos = self.get_local_position()[0:2]
        # If we got a scale factor, indicate to the user that calibration is
        # done
        if self.scanner.scene.set_second_point(xypos):
            self.on_scanner_calibration_complete()
        self.scanner_calibration_p2_text.set_markup('<span weight="light" font_desc="Bebas 12" font_stretch="ultracondensed" foreground="white" >P1    :    (   %s  ,  %s    )</span>' % (self.dro_long_format, self.dro_long_format) % tuple(xypos))
        self.scanner_calibration_scale_text.set_markup('<span weight="light" font_desc="Bebas 12" font_stretch="ultracondensed" foreground="white" >Scale   :   %s   ,   Angle  :  %s  &#xB0;  </span>' % (self.dro_long_format, self.dro_long_format) % (self.scanner.scene.scale,self.scanner.scene.angle))

    def on_scanner_calibration_zoom_p1_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # zoom the area around P1 to finish jogging target
        if self.scanner.zoom_state == 'p1':
            #self.set_image('scanner_zoom_p1_on_off_image', 'button_zoom_p1_off.png')
            self.scanner.zoom_state = 'off'
        else:
            #self.set_image('scanner_zoom_p1_on_off_image', 'button_zoom_p1_on.png')
            self.scanner.zoom_state = 'p1'

    def on_scanner_calibration_zoom_p2_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # zoom the area around P1 to finish jogging target
        if self.scanner.zoom_state == 'p2':
            #self.set_image('scanner_zoom_p2_on_off_image', 'button_zoom_p2_off.png')
            self.scanner.zoom_state = 'off'
        else:
            #self.set_image('scanner_zoom_p2_on_off_image', 'button_zoom_p2_on.png')
            self.scanner.zoom_state = 'p2'

    def scanner_display_scanpoints(self):
        """ Using the scanner's internal state, display useful information in the Scan window"""
        # Get local arguments
        points_label = self.get_obj('scanner_scan_points_label')
        rows_label = self.get_obj('scanner_scan_rows_label')
        time_label = self.get_obj('scanner_scan_time_label')

        points_label.set_markup(self.format_dro_string('Points: {0}'.format(self.scanner.scene.points_count),11))
        rows_label.set_markup(self.format_dro_string('Rows: {0} , Columns: {1}'.format(self.scanner.scene.rows,self.scanner.scene.columns),11))
        time_data=datetime.timedelta(seconds=round(self.scanner.scene.estimated_time))
        time_label.set_markup(self.format_dro_string('Estimated Time: {0}'.format(time_data),11))

    def on_scanner_update_bounds(self, index, value):
        if self.scanner is not None and self.scanner.camera is not None:
            self.scanner.scene.bounds[index] = value
            self.scanner.scene.update_scanpoints(self.scanner.camera.get_frame_size())
            self.scanner_display_scanpoints()
        return

    #TODO come up with a cleaner way to do parameter validation here, maybe a standard set of validation params for each DRO?
    # i.e. each parameter has an associated min / max value, data type, etc.
    def on_scanner_scan_x_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        # Have a valid numerical value
        (in_limits, error_msg) = self.validate_local_position(value,0)
        if not valid or not in_limits:
            mill_conversational.raise_alarm(widget)
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        mill_conversational.raise_alarm(widget, False)
        widget.set_text(self.dro_long_format % value)
        self.on_scanner_update_bounds(0, value)
        self.scanner_scan_dro_list['scanner_scan_x_end_dro'].grab_focus()

    def on_scanner_scan_x_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        (in_limits, error_msg) = self.validate_local_position(value,0)
        if not valid or not in_limits:
            mill_conversational.raise_alarm(widget)
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        mill_conversational.raise_alarm(widget, False)
        widget.set_text(self.dro_long_format % value)
        self.on_scanner_update_bounds(1, value)
        self.scanner_scan_dro_list['scanner_scan_y_start_dro'].grab_focus()
        return

    def on_scanner_scan_y_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        (in_limits, error_msg) = self.validate_local_position(value,1)
        if not valid or not in_limits:
            mill_conversational.raise_alarm(widget)
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.on_scanner_update_bounds(2, value)
        self.scanner_scan_dro_list['scanner_scan_y_end_dro'].grab_focus()

    def on_scanner_scan_y_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        (in_limits, error_msg) = self.validate_local_position(value,1)
        if not valid or not in_limits:
            mill_conversational.raise_alarm(widget)
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.on_scanner_update_bounds(3, value)
        self.window.set_focus(None)

    def on_scanner_scan_tolerance_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.scanner_scan_dro_list['scanner_scan_feature_size_dro'].grab_focus()

    def on_scanner_scan_feature_size_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_short_format % value)
        self.scanner_scan_dro_list['scanner_scan_x_start_dro'].grab_focus()

    def on_scanner_scope_capture_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # capture current X and Y and store in table
        #scope_pos = self.status.actual_position
        abs_pos = self.status.position
        scope_pos = self.to_local_position(abs_pos)

        scope_x = ('%0.4f' % scope_pos[0])
        scope_y = ('%0.4f' % scope_pos[1])
        #print "--kw scope x y = ", scope_x, scope_y
        self.scope_liststore[self.scope_row][1] = scope_x
        self.scope_liststore[self.scope_row][2] = scope_y
        self.scope_row += 1

    def on_scope_x_column_edited(self, cell, row, value, model):
        # TODO - connect to mill_conversational.validate_param
        #valid, value, error_msg = mill_conversational.validate_param(value)
        #if not valid:
        #    self.error_handler(error_msg, ALARM_LEVEL_LOW)
        #    return

        print "Editing X column : on_scope"
        if value == '' or value == '??':
            model[row][1] = ""
            return
        try:
            value = float(value)
        except ValueError:
            self.error_handler.write("Invalid position specified for drill table", ALARM_LEVEL_LOW)

        row = 0 if row == '' else int(row)
        model[row][1] = "%0.4f" % value

    def on_scope_y_column_edited(self, cell, row, value, model):
        # TODO - connect to mill_conversational.validate_param
        #valid, value, error_msg = mill_conversational.validate_param(value)
        #if not valid:
        #    self.error_handler(error_msg, ALARM_LEVEL_LOW)
        #    return

        print "Editing Y column : on_scope"
        if value == '' or value == '??':
            model[row][2] = ""
            return
        try:
            value = float(value)
        except ValueError:
            self.error_handler.write("Invalid position specified for drill table", ALARM_LEVEL_LOW)

        row = 0 if row == '' else int(row)
        model[row][2] = "%0.4f" % value

    # ~~~~~~ Scanner Common DROs, Buttons and Bows
    def on_scanner_common_working_fov_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_short_format % value)
        #self.scanner_scan_dro_list['scanner_scan_x_start_dro'].grab_focus()
        return


    # Position/Status Readout Group

    # common dro callbacks

    def on_dro_gets_focus(self, widget, event):
        if self.moving() or not widget.has_focus():
            return
        widget.prev_val = widget.get_text()
        widget.modify_base(gtk.STATE_NORMAL, gtk.gdk.Color(HIGHLIGHT))
        widget.modify_text(gtk.STATE_NORMAL, gtk.gdk.Color('black'))
        if not widget.masked:
            # only highlight the whole field if the user hasn't selected a portion of it
            widget.select_region(0, -1)

        widget.masked = True

        if self.touchscreen_enabled:
            numpad.numpad_popup(widget)
            widget.masked = 0
            widget.select_region(0, 0)
            self.window.set_focus(None)

    def on_dro_loses_focus(self, widget, data=None):
        if widget_in_alarm_state(widget): return
        widget.modify_base(gtk.STATE_NORMAL, gtk.gdk.Color('white'))
        widget.modify_text(gtk.STATE_NORMAL, gtk.gdk.Color('black'))
        if not self.touchscreen_enabled:
            widget.masked = False
            widget.select_region(0, 0)

    def on_dro_key_press_event(self, widget, event, data=None):
        kv = event.keyval
        if kv == gtk.keysyms.Escape:
            widget.modify_base(gtk.STATE_NORMAL, gtk.gdk.Color('white'))
            widget.modify_text(gtk.STATE_NORMAL, gtk.gdk.Color('black'))
            widget.masked = False
            self.window.set_focus(None)
            return True

    def on_qwerty_dro_gets_focus(self, widget, data=None):
        if self.touchscreen_enabled:
            numpad.numpad_popup(widget, True)
            self.window.set_focus(None)
            return True


    def on_conv_dro_gets_focus(self, widget, data=None):
        # really the button release event
        widget.prev_val = widget.get_text()
        widget.select_region(0, -1)
        if self.touchscreen_enabled:
            keypad = numpad.numpad_popup(widget)
            widget.select_region(0, 0)
            self.window.set_focus(None)

    def on_dro_focus_in_event(self, widget, data=None):
        widget.prev_val = widget.get_text()

    # ref button callbacks


    def on_ref_x_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # check if door sw is enabled and warn user about wiring change
        if self.door_sw_enabled:
            # have we already warned the user about door sw wiring?
            try:
                show_warning = self.redis.hget('machine_prefs', 'display_door_sw_x_ref_warning') == 'True'
            except:
                # redis key doesn't exist, assume we want to display this
                show_warning = True
                self.redis.hset('machine_prefs', 'display_door_sw_x_ref_warning', 'True')
            if show_warning:
                dialog = tormach_file_util.ok_cancel_popup('enclosure    door   switch    is    enabled    on    settings    screen.   has    switch    been    installed    and    wiring    changes    been    made?');
                dialog.run()
                response = dialog.response;
                dialog.destroy()
                if response != gtk.RESPONSE_OK :
                    return
                self.redis.hset('machine_prefs', 'display_door_sw_x_ref_warning', 'False')

        self.ref_axis(0)



    def on_ref_y_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.ref_axis(1)

    def on_ref_z_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.ref_axis(2)


    def on_ref_a_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.ref_axis(3)

    def on_usbio_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return

        current_usbio_button = gtk.Buildable.get_name(widget)
        #fetch digit character within usbio_output_#_led
        index = current_usbio_button[USBIO_STR_DIGIT_INDEX]

        if self.hal["usbio-output-" + index]: #if relay on
            command = 'M65 P' + index  #turn off
        else:
            command = 'M64 P' + index  #turn on

        self.issue_mdi(command)



    def ref_axis(self, axis):
        axis_dict = {0:'X', 1:'Y', 2:'Z', 3:'A'}

        # make sure we're not on a limit right now!
        if (self.status.limit[axis] == 3) and self.home_switches_enabled:
            self.error_handler.write("Cannot    reference    this    axis    when    on    a    limit    switch.    Move    the    machine    off   limit    switch    before    proceeding.")
            return

        # kludge for issue #1115:
        if axis == 0 and self.door_sw_enabled and self.home_switches_enabled:
            if self.status.limit[1] == 3:
                self.error_handler.write("Cannot    reference    this    axis    when    on    a    limit    switch.    Move    the    machine    off   limit    switch    before    proceeding.")
                return

        # warn if about to re-reference
        if self.status.homed[axis]:
            dialog = tormach_file_util.ok_cancel_popup(axis_dict[axis] + '    axis    already    homed.    Re-home?');
            dialog.run()
            response = dialog.response;
            dialog.destroy()
            if response != gtk.RESPONSE_OK :
                return

        if self.door_sw_enabled:
            # queue these buttons using atc queue
            self.atc.queue_ref_axis(axis)
        elif axis == 2:
            # always ref z through ATC code to prevent ref with tray in
            self.atc.ref_z()
        else:
            self.ensure_mode(linuxcnc.MODE_MANUAL)
            self.command.home(axis)


    # Zero DRO callbacks

    def on_zero_x_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.set_work_offset("X", 0)

    def on_zero_y_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.set_work_offset("Y", 0)

    def on_zero_z_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.set_work_offset("Z", 0)

    def on_zero_a_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.set_work_offset("A", 0)

    # dro events

    def on_x_dro_activate(self, widget):
        valid, dro_val, error_msg = self.conversational.validate_x_point(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        self.set_work_offset("X", dro_val)
        # allow updates
        widget.masked = False
        self.window.set_focus(None)

    def on_y_dro_activate(self, widget):
        valid, dro_val, error_msg = self.conversational.validate_y_point(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        self.set_work_offset("Y", dro_val)
        # allow updates
        widget.masked = False
        self.window.set_focus(None)


    def on_z_dro_activate(self, widget):
        valid, dro_val, error_msg = self.conversational.validate_z_point(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        self.set_work_offset("Z", dro_val)
        # allow updates
        widget.masked = False
        self.window.set_focus(None)


    def on_a_dro_activate(self, widget):
        valid, dro_val, error_msg = self.conversational.validate_z_point(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        self.set_work_offset("A", dro_val)
        # allow updates
        widget.masked = False
        self.window.set_focus(None)

    def on_spindle_rpm_dro_activate(self, widget, data=None):
        # unmask DRO
        widget.masked = False
        # user entry validation
        valid, dro_val, error_msg = self.conversational.validate_max_spindle_rpm(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        rpm = abs(dro_val)
        s_command = "S%.0f" % (rpm)
        self.issue_mdi(s_command)
        self.window.set_focus(None)


    def on_feed_per_min_dro_activate(self, widget, data=None):
        # get DRO value
        valid, dro_val, error_msg = self.conversational.validate_feedrate(widget, self.g21)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        feed_per_min = abs(dro_val)
        if feed_per_min > self.max_feedrate * self.get_linear_scale():
            feed_per_min = self.max_feedrate * self.get_linear_scale()
            self.error_handler.write("Clipping feedrate to maximum allowed value for the machine.", ALARM_LEVEL_LOW)
        # TODO - do we need the explicit G94 here?
        g94_command = "G94 F%.4f" % (feed_per_min)
        self.issue_mdi(g94_command)
        # unmask DROs
        widget.masked = False
        self.window.set_focus(None)


    # Manual Control Group
    def on_key_press_or_release(self, widget, event, data=None):
        kv = event.keyval

        #print 'event.statekeyval: %d 0x%04x' % (kv, kv)
        #print 'event.statestate:  %d 0x%04x' % (event.state, event.state)
        
        # Probing Buttons
        if kv == gtk.keysyms.F9 and event.type == gtk.gdk.KEY_RELEASE and self.current_notebook_page == PROBE_PAGE:
			probing.find_corner_northwest(self)

        if kv == gtk.keysyms.F10 and event.type == gtk.gdk.KEY_RELEASE and self.current_notebook_page == PROBE_PAGE:
			probing.find_corner_northeast(self)
				
        if kv == gtk.keysyms.F11 and event.type == gtk.gdk.KEY_RELEASE and self.current_notebook_page == PROBE_PAGE:
			probing.find_corner_southeast(self)	

        if kv == gtk.keysyms.F12 and event.type == gtk.gdk.KEY_RELEASE and self.current_notebook_page == PROBE_PAGE:
			probing.find_corner_southwest(self)				
					
        # Utilities
        if kv == gtk.keysyms.F1 and event.type == gtk.gdk.KEY_PRESS:
            # If we're not on the status page, save the current page and switch
            # to the status page
            # The logic is a little convoluted because auto-repeat of keys ends up
            # sending us a lot of KEY_PRESS events, but only one KEY_RELEASE.
            # F1_page_toggled gives us enough info so that if you're on the MILL_STATUS_PAGE
            # and hold down F1, then upon its release, we don't switch back to whatever
            # happens to be laying around in prev_page.  Effectively F1 hold is
            # ignored when you're on the MILL_STATUS_PAGE page entirey.
            if self.current_notebook_page != MILL_STATUS_PAGE:
                self.F1_page_toggled = True
                self.prev_notebook_page = self.current_notebook_page
                self.notebook.set_current_page(MILL_STATUS_PAGE)

        if kv == gtk.keysyms.F1 and event.type == gtk.gdk.KEY_RELEASE:
            if self.F1_page_toggled:
                self.F1_page_toggled = False
                self.notebook.set_current_page(self.prev_notebook_page)

        if kv == gtk.keysyms.Print and event.type == gtk.gdk.KEY_PRESS:
            self.screen_grab()
            #FIXME should this return here? Not sure if anything else needs "Print" key

        # open new terminal window
        # MOD1_MASK indicates the left Alt key pressed
        # CONTROL_MASK indicates either Ctrl key is pressed
        if event.state & gtk.gdk.MOD1_MASK and event.state & gtk.gdk.CONTROL_MASK:
            if kv in [gtk.keysyms.x, gtk.keysyms.X] and event.type == gtk.gdk.KEY_PRESS:
                # start a terminal window in $HOME directory
                subprocess.Popen(args=["gnome-terminal", "--working-directory=" + os.getenv('HOME')]).pid
                return True


        # Keyboard functions
        # Return True on TAB to prevent tabbing focus changes
        if kv == gtk.keysyms.Tab:
            return True

        # Disable jogging and pass through depending on focus
        if kv in self.jogging_keys:

            #First, handle specific cases that don't behave by type rules

            # no jogging while mdi line has focus
            if self.mdi_line_masked:
                # Make sure to pass through key presses to navigate MDI
                return False if kv in self.mdi_mask_keys else True

            # Next, check the type of the current focused item and pass through
            # keys if needed

            focused_item = type(self.window.get_focus())
            if focused_item in self.key_mask:
                return False if kv in self.key_mask[focused_item] else True

            # Have to disregard jogging when the scanner is running since it
            # executes moves via MDI mode (jogging will mess this up if it is
            # not disabled)
            if self.scanner and self.scanner.moving():
                return True

        # Preconditions checked -  Jogging handled below
        # check to see if we're releasing the key

        # Force jogging to stop whenever shift keys are pressed or released
        # (Mach3 Style)
        if kv in [gtk.keysyms.Shift_L, gtk.keysyms.Shift_R] and not self.program_running() and self.moving():
            self.stop_all_jogging()
            return True

        if event.type == gtk.gdk.KEY_RELEASE and (kv in self.jogging_keys or kv in self.mykeys):
            self.jogging_key_pressed[kv] = False
            # right or left - x axis
            if kv ==  gtk.keysyms.Left or kv == gtk.keysyms.Right:
                jog_axis = 0
            # up or down - y axis
            elif kv == gtk.keysyms.Up or kv == gtk.keysyms.Down:
                jog_axis = 1
            # page up or page down - z axis
            elif kv == gtk.keysyms.Prior or kv == gtk.keysyms.Next:
                jog_axis = 2
            elif kv == gtk.keysyms.comma or kv == gtk.keysyms.period:
                jog_axis = 3
            else:
                return False

            if (self.jog_mode == linuxcnc.JOG_CONTINUOUS) and not self.program_running():
                self.stop_jog(jog_axis)
            return True

        elif ( 
	    event.type == gtk.gdk.KEY_PRESS 
	    and (kv in self.jogging_keys or kv in self.mykeys)
	    ):
            #print self.jogging_key_pressed
            if kv == gtk.keysyms.Right:
                # right arrow - X positive
                jog_axis = 0
                jog_direction = 1
            elif kv == gtk.keysyms.Left:
                jog_axis = 0
                jog_direction = -1
            elif kv == gtk.keysyms.Up:
                jog_axis = 1
                jog_direction = 1
            elif kv == gtk.keysyms.Down:
                jog_axis = 1
                jog_direction = -1
            elif kv == gtk.keysyms.Prior:
                jog_axis = 2
                jog_direction = 1
            elif kv == gtk.keysyms.Next:
                jog_axis = 2
                jog_direction = -1
            elif kv == gtk.keysyms.period:
                jog_axis = 3
                jog_direction = 1
            elif kv == gtk.keysyms.comma:
                jog_axis = 3
                jog_direction = -1
	    elif event.state & gtk.gdk.MOD1_MASK:
		if kv == gtk.keysyms.l and self.jog_mode == linuxcnc.JOG_INCREMENT:
			jog_axis=0
			jog_direction=1
	    	if kv == gtk.keysyms.j and self.jog_mode == linuxcnc.JOG_INCREMENT:
			jog_axis=0
			jog_direction=-1
		if kv == gtk.keysyms.i and self.jog_mode == linuxcnc.JOG_INCREMENT:
			jog_axis=1
			jog_direction=1
	    	if kv == gtk.keysyms.k and self.jog_mode == linuxcnc.JOG_INCREMENT:
			jog_axis=1
			jog_direction=-1
		if kv == gtk.keysyms.p and self.jog_mode == linuxcnc.JOG_INCREMENT:
			jog_axis=2
			jog_direction=-1
	    	if kv == gtk.keysyms.o and self.jog_mode == linuxcnc.JOG_INCREMENT:
			jog_axis=2
			jog_direction=1
            # After determining the axis and direction, run the jog iff the key
            # is not already depressed

            jogging_rapid = event.state & gtk.gdk.SHIFT_MASK

            if not self.jogging_key_pressed[kv]:
                self.set_jog_mode(self.keyboard_jog_mode)
                self.jog(jog_axis, jog_direction, self.jog_speeds[jog_axis], not jogging_rapid)
            # Update the state of the pressed key
            self.jogging_key_pressed[kv]=True
            return True

        # Handle feed hold
        if kv == gtk.keysyms.space and self.moving():
            self.enqueue_button_press_release(self.button_list['feedhold'])
            return True

	if kv==gtk.keysyms._1 and event.state & gtk.gdk.CONTROL_MASK:
		self.enqueue_button_press_release(self.button_list['zero_x'])	    
		return True	

	if kv==gtk.keysyms._2 and event.state & gtk.gdk.CONTROL_MASK:
		self.on_dro_gets_focus(self.dro_list['x_dro'], None)
		self.dro_list['x_dro'].grab_focus()

	if kv==gtk.keysyms._3 and event.state & gtk.gdk.CONTROL_MASK:
		self.enqueue_button_press_release(self.button_list['zero_y'])	    
		return True	

	if kv==gtk.keysyms._4 and event.state & gtk.gdk.CONTROL_MASK:
		self.on_dro_gets_focus(self.dro_list['y_dro'], None)
		self.dro_list['y_dro'].grab_focus()
		return True

	if kv==gtk.keysyms._5 and event.state & gtk.gdk.CONTROL_MASK:
		self.enqueue_button_press_release(self.button_list['zero_z'])	    
		return True	

	if kv==gtk.keysyms._6 and event.state & gtk.gdk.CONTROL_MASK:
		self.on_dro_gets_focus(self.dro_list['z_dro'], None)
		self.dro_list['z_dro'].grab_focus()
		return True

	if kv==gtk.keysyms._7 and event.state & gtk.gdk.CONTROL_MASK:
		self.on_tool_dro_gets_focus(self.dro_list['tool_dro'], None)
		self.dro_list['tool_dro'].grab_focus()
		return True

	if kv==gtk.keysyms._8 and event.state & gtk.gdk.CONTROL_MASK:
		self.enqueue_button_press_release(self.button_list['jog_0001'])
		return True
	
	if kv==gtk.keysyms._9 and event.state & gtk.gdk.CONTROL_MASK:
		self.enqueue_button_press_release(self.button_list['jog_0010'])
		return True

	if kv==gtk.keysyms._0 and event.state & gtk.gdk.CONTROL_MASK:
		self.enqueue_button_press_release(self.button_list['jog_0100'])
		return True

	if kv==gtk.keysyms.minus and event.state & gtk.gdk.CONTROL_MASK:
		self.enqueue_button_press_release(self.button_list['jog_1000'])
		return True


	if kv==gtk.keysyms.h and event.state & gtk.gdk.MOD1_MASK:
	    self.enqueue_button_press_release(self.button_list['jog_inc_cont'])
	    return True

	if kv==gtk.keysyms._1 and event.state & gtk.gdk.MOD1_MASK:	
	    curr_feed_override=self.feedrate_override_adjustment.get_value()
	    if not curr_feed_override<=0: 
		if curr_feed_override<=20:
			self.feedrate_override_adjustment.set_value(int(curr_feed_override)-1)
		else:		
			self.feedrate_override_adjustment.set_value(int(curr_feed_override)-5)
	    return True

	if kv==gtk.keysyms._2 and event.state & gtk.gdk.MOD1_MASK:
	    curr_feed_override=self.feedrate_override_adjustment.get_value()
	    if not curr_feed_override>=150: 
		if curr_feed_override<=19:
			self.feedrate_override_adjustment.set_value(int(curr_feed_override)+1)
		else:		
			self.feedrate_override_adjustment.set_value(int(curr_feed_override)+5)
	    return True
		
	if kv==gtk.keysyms._9 and event.state & gtk.gdk.MOD1_MASK:	
	    self.enqueue_button_press_release(self.button_list['feedrate_override'])
	    return True
		
	if kv==gtk.keysyms._3 and event.state & gtk.gdk.MOD1_MASK:
	    curr_spindle_override=self.spindle_override_adjustment.get_value()
	    if not curr_spindle_override<=0:
		self.spindle_override_adjustment.set_value(int(curr_spindle_override)-5)
	    return True
	
	if kv==gtk.keysyms._4 and event.state & gtk.gdk.MOD1_MASK:
	    curr_spindle_override=self.spindle_override_adjustment.get_value()
	    if not curr_spindle_override>=150: 
		self.spindle_override_adjustment.set_value(int(curr_spindle_override)+5)
	    return True
		
	if kv==gtk.keysyms._0 and event.state & gtk.gdk.MOD1_MASK:	
	    self.enqueue_button_press_release(self.button_list['rpm_override'])
	    return True
	
	if kv==gtk.keysyms._5 and event.state & gtk.gdk.MOD1_MASK:
	    curr_maxvel_override=self.maxvel_override_adjustment.get_value()
	    if not curr_maxvel_override<=0: 
		if curr_maxvel_override<=20:
			self.maxvel_override_adjustment.set_value(int(curr_maxvel_override)-1)
		else:		
			self.maxvel_override_adjustment.set_value(int(curr_maxvel_override)-5)
	    return True
	
	if kv==gtk.keysyms._6 and event.state & gtk.gdk.MOD1_MASK:
	    curr_maxvel_override=self.maxvel_override_adjustment.get_value()
	    if not curr_maxvel_override>=100: 
		if curr_maxvel_override<=19:
			self.maxvel_override_adjustment.set_value(int(curr_maxvel_override)+1)
		else:		
			self.maxvel_override_adjustment.set_value(int(curr_maxvel_override)+5)
	    return True
		
	if kv==gtk.keysyms.minus and event.state & gtk.gdk.MOD1_MASK:	
	    self.enqueue_button_press_release(self.button_list['maxvel_override'])
	    return True
	
	if kv==gtk.keysyms._7 and event.state & gtk.gdk.MOD1_MASK:
	    curr_jogspeed_override=self.jog_speed_adjustment.get_value()
	    if not curr_jogspeed_override>=150: 
		self.jog_speed_adjustment.set_value(curr_jogspeed_override-2)
	    return True

	if kv==gtk.keysyms._8 and event.state & gtk.gdk.MOD1_MASK:
	    curr_jogspeed_override=self.jog_speed_adjustment.get_value()
	    if not curr_jogspeed_override<=0: 
		self.jog_speed_adjustment.set_value(curr_jogspeed_override+2)
	    print int(curr_jogspeed_override)
	    return True	

        # Escape key for stop
        if kv == gtk.keysyms.Escape:
            self.enqueue_button_press_release(self.button_list['stop'])
            return True


        # alt key shortcuts
        # MOD1_MASK indicates the left alt key pressed
        # MOD5_MASK indicates the right alt key pressed
        if event.state & (gtk.gdk.MOD1_MASK | gtk.gdk.MOD5_MASK) and event.type == gtk.gdk.KEY_RELEASE:

            # alt-e, edit current gcode program
            if kv in [gtk.keysyms.e, gtk.keysyms.E]:
                # cannot enqueue edit_gcode button press - it only works after File tab has been opened
                path = self.current_gcode_file_path
                if not self.moving():
                    if path != '':
                        self.edit_gcode_file(path)
                    else:
                        # open gedit with empty file
                        try:
                            # run the editor, store the pid somewhere in case of crash
                            self.editor_pid = subprocess.Popen([self.gcode_edit_program_to_run]).pid
                        except OSError:
                            self.error_handler.write("OSError exception raised. Could not run edit program: %s" % self.gcode_edit_program_to_run, ALARM_LEVEL_LOW)

            #smart cool releases -  when alt key comes up cancel actions
            if self.smart_overriding:
                self.hal['smart-cool-up'] = self.hal['smart-cool-down'] = self.smart_overriding = False


            if kv in [gtk.keysyms.c, gtk.keysyms.C]:  # cancel manual smart cool control mode
                self.hal['smart-cool-man-auto'] = False

            if kv in [gtk.keysyms.m, gtk.keysyms.M]:  #mist on/off toggle
                self.hal['mist'] = not self.hal['mist']


            # alt-enter to set focus to MDI line
            # must only work when the Main tab is showing
            if self.current_notebook_page == MAIN_PAGE and kv == gtk.keysyms.Return and not self.program_running():
                self.on_mdi_line_gets_focus(self.mdi_line, None)
                self.mdi_line.grab_focus()

            for (k_val, k_widget) in self.alt_keyboard_shortcuts:
                if kv == k_val:
                    self.enqueue_button_press_release(k_widget)

        if event.state & (gtk.gdk.MOD1_MASK | gtk.gdk.MOD5_MASK) and event.type == gtk.gdk.KEY_PRESS:

            #smart cool presses

            if kv in [gtk.keysyms.u, gtk.keysyms.U]:  # nozzle up
                self.hal['smart-cool-up'] = self.smart_overriding = self.hal['smart-cool-man-auto'] = True


            if kv in [gtk.keysyms.d, gtk.keysyms.D]:  # nozzle down
                self.hal['smart-cool-down'] = self.smart_overriding = self.hal['smart-cool-man-auto'] = True






        # ctrl key shortcuts
        # CONTROL_MASK indicates the left ctrl key pressed
        if event.state & gtk.gdk.CONTROL_MASK and event.type == gtk.gdk.KEY_RELEASE:
            for (k_val, k_widget) in self.ctrl_keyboard_shortcuts:
                if kv == k_val:
                    self.enqueue_button_press_release(k_widget)

        return False

    def set_jog_mode(self, mode):
        """Wrapper function to ensure that jog mode is cleanly switched from continous to stepping.
            This prevents the jog mode from being changed in the middle of a
            move, which can lead to runaway jogging.
        """
        if self.jog_mode == mode:
            return True
        if not self.moving():
            #Ok to switch since we're not moving
            self.jog_mode = mode
            return True
        elif self.jog_mode == linuxcnc.JOG_INCREMENT:
            #Safe to switch since step mode is limited distance
            self.jog_mode = mode
            return True

        return False

    def set_keyboard_jog_mode(self, mode):
        """Wrapper function to ensure that jog mode is cleanly switched from continous to stepping.
            This prevents the jog mode from being changed in the middle of a
            move, which can lead to runaway jogging.
        """
        # keep track of keyboard mode with separate variable so we can force it in keyboard jog handler
        self.keyboard_jog_mode = mode
        if self.jog_mode == mode:
            return True
        if not self.moving():
            # button art
            if mode == linuxcnc.JOG_CONTINUOUS:
                self.set_image('jog_inc_cont_image', 'jog_cont_green.png')
            else:
                self.set_image('jog_inc_cont_image', 'jog_step_green.png')
            #Ok to switch since we're not moving
            self.jog_mode = mode
            return True
        elif self.jog_mode == linuxcnc.JOG_INCREMENT:
            #Safe to switch since step mode is limited distance
            self.jog_mode = mode
            return True

        return False


    def on_mouse_wheel_event(self, widget, event):
        return True

    def on_jogging_scale_gets_focus(self, widget, data=None):
        self.set_keyboard_jog_mode(linuxcnc.JOG_CONTINUOUS)

    def clear_jog_LEDs(self):
        # turn all the JOG button LEDs "off"
        if self.g21:
            self.set_image('jog_0001_image', 'Metric-0025-Black.jpg')
            self.set_image('jog_0010_image', 'Metric-010-Black.jpg')
            self.set_image('jog_0100_image', 'Metric-100-Black.jpg')
            self.set_image('jog_1000_image', 'Metric-1.00-Black.jpg')
        else:
            self.set_image('jog_0001_image', '0001-Pressed-Black.jpg')
            self.set_image('jog_0010_image', '0010-Pressed-Black.jpg')
            self.set_image('jog_0100_image', '0100-Pressed-Black.jpg')
            self.set_image('jog_1000_image', '1000-Pressed-Black.jpg')

    def set_jog_LEDs(self):
        if self.jog_increment == 0.0001:
            self.hal['jog-gui-step-index'] = 0
            if self.g21:
                self.set_image('jog_0001_image', 'Metric-0025-Green.jpg')
            else:
                self.set_image('jog_0001_image', '0001-Pressed-Green.jpg')
        elif self.jog_increment == 0.001:
            self.hal['jog-gui-step-index'] = 1
            if self.g21:
                self.set_image('jog_0010_image', 'Metric-010-Green.jpg')
            else:
                self.set_image('jog_0010_image', '0010-Pressed-Green.jpg')
        elif self.jog_increment == 0.01:
            self.hal['jog-gui-step-index'] = 2
            if self.g21:
                self.set_image('jog_0100_image', 'Metric-100-Green.jpg')
            else:
                self.set_image('jog_0100_image', '0100-Pressed-Green.jpg')
        elif self.jog_increment == 0.1:
            self.hal['jog-gui-step-index'] = 3
            if self.g21:
                self.set_image('jog_1000_image', 'Metric-1.00-Green.jpg')
            else:
                self.set_image('jog_1000_image', '1000-Pressed-Green.jpg')

    def on_jog_speed_adjustment_value_changed(self, adjustment):
        self.jog_speed_label.set_text(str(int(adjustment.value))+"%")
        self.set_keyboard_jog_mode(linuxcnc.JOG_CONTINUOUS)
        self.jog_override_pct = (adjustment.value) / 100.0

    def on_jog_inc_cont_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        print "jog mode was: ", self.jog_mode
        if self.jog_mode == linuxcnc.JOG_INCREMENT:
            self.set_keyboard_jog_mode(linuxcnc.JOG_CONTINUOUS)
        else:
            self.set_keyboard_jog_mode(linuxcnc.JOG_INCREMENT)

    def jog_button_release_handler(self, widget, jog_increment, jog_index):
        if not self.check_button_permissions(widget): return False
        if not self.set_keyboard_jog_mode(linuxcnc.JOG_INCREMENT): return False
        self.clear_jog_LEDs()
        self.jog_increment = jog_increment
        self.hal['jog-gui-step-index'] = jog_index
        print 'jog increment: %3.4F' % self.jog_increment
        return True

    def on_jog_0001_button_release_event(self, widget, data=None):
        if not self.jog_button_release_handler(widget, 0.0001, 0): return
        button_image = '0001-Pressed-Green.jpg' if not self.g21 else 'Metric-0025-Green.jpg'
        self.set_image('jog_0001_image', button_image)

    def on_jog_0010_button_release_event(self, widget, data=None):
        if not self.jog_button_release_handler(widget, 0.001, 1): return
        button_image = '0010-Pressed-Green.jpg' if not self.g21 else 'Metric-010-Green.jpg'
        self.set_image('jog_0010_image', button_image)

    def on_jog_0100_button_release_event(self, widget, data=None):
        if not self.jog_button_release_handler(widget, 0.01, 2): return
        button_image = '0100-Pressed-Green.jpg' if not self.g21 else 'Metric-100-Green.jpg'
        self.set_image('jog_0100_image', button_image)

    def on_jog_1000_button_release_event(self, widget, data=None):
        if not self.jog_button_release_handler(widget, 0.1, 3): return
        button_image = '1000-Pressed-Green.jpg' if not self.g21 else 'Metric-1.00-Green.jpg'
        self.set_image('jog_1000_image', button_image)

    def on_ccw_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        if self.notebook.get_current_page() != MAIN_PAGE:
            self.error_handler.write("Cannot start spindle while not on Main screen", ALARM_LEVEL_LOW)
            return
        # Per conversation with John, better to do this with command.spindle_fwd
        # quick look at touchy/axis makes me think that there's no way to set
        # spindle speed in MODE_MANUAL.
        # don't issue MDI command if speed is zero
        if self.s_word != 0.0:
            self.issue_mdi("m4")

    def on_spindle_stop_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # do not use command.spindle(0) because it steps on status.settings[2]
        self.issue_mdi("m5")

    def on_cw_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        if self.notebook.get_current_page() != MAIN_PAGE:
            self.error_handler.write("Cannot start spindle while not on Main screen", ALARM_LEVEL_LOW)
            return
        # don't issue MDI command if speed is zero
        if self.s_word != 0.0:
            self.issue_mdi("m3")

    def on_spindle_range_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        if self.program_running(True):
            # do not allow this button while a program is running
            self.error_handler.write("Cannot change spindle range while a program is running", ALARM_LEVEL_LOW)
            return
        if self.hal['spindle-range']:
            # we're in high gear, so make it lo
            self.hal['spindle-range'] = 0
            self.set_image('spindle_range_image', 'Spindle_Range_LO_Highlight.png')
            self.redis.hset('machine_prefs', 'spindle_range', 'lo')
        else:
            self.hal['spindle-range'] = 1
            self.set_image('spindle_range_image', 'Spindle_Range_HI_Highlight.png')
            self.redis.hset('machine_prefs', 'spindle_range', 'hi')


    def on_tool_dro_gets_focus(self, widget, data=None):
        if self.moving():
            return
        self.set_image('m6_g43_image', 'M6_G43_Highlight.png')
        widget.modify_base(gtk.STATE_NORMAL, gtk.gdk.Color(HIGHLIGHT))
        widget.modify_text(gtk.STATE_NORMAL, gtk.gdk.Color('black'))
        widget.masked = True
        widget.select_region(0, -1)
        if self.touchscreen_enabled:
            keypad = numpad.numpad_popup(widget)
            widget.masked = 0
            widget.select_region(0, 0)
            self.window.set_focus(None)


    def on_tool_dro_loses_focus(self, widget, data=None):
        self.set_image('m6_g43_image', 'M6_G43.png')
        if widget_in_alarm_state(widget): return
        widget.modify_base(gtk.STATE_NORMAL, gtk.gdk.Color('white'))
        widget.modify_text(gtk.STATE_NORMAL, gtk.gdk.Color('black'))
        if not self.touchscreen_enabled:
            widget.masked = False
            widget.select_region(0, 0)


    def on_tool_dro_activate(self, widget, data=None):
        # get DRO value
        valid, tool_num, error_msg = self.conversational.validate_tool_number(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            widget.masked = 0
            return
        self.dro_list['tool_dro'].set_text("%1d" % tool_num)
        widget.masked = 0
        self.on_m6_g43_button_release_event(self.button_list['m6_g43'])
        self.tt_scroll_adjust(tool_num)


    def on_m6_g43_focus_in_event(self, widget, data=None):
        # keep tool dro from getting overwritten by periodic function until M6 is  called.
        self.dro_list['tool_dro'].masked = 1

    def on_m6_g43_focus_out_event(self, widget, data=None):
        self.dro_list['tool_dro'].masked = 0
        self.set_image('m6_g43_image', 'M6_G43.png')

    def on_m6_g43_button_release_event(self, widget, data=None):
        self.check_button_permissions(self.button_list['m6_g43'])
        current_tool = self.status.tool_in_spindle

        # TODO - better validation here
        valid, tool_num, error_msg = self.conversational.validate_tool_number(self.dro_list['tool_dro'])
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        if tool_num == current_tool:
            # still might want to apply the offset
            # TODO - check to see if offset is already correctly applied
            self.issue_mdi('G43')
            return




        # if we've got an ATC, and the user enters a number in the new tool dro that is a tray tool
        # ask if they want to fetch the tool from the tray or just M61 to make it active
        old_tool_in_tray = new_tool_in_tray = invoke_atc = False  #default until we know better
        if self.atc.operational:
            self.status.poll()
            if self.atc.lookup_slot(self.status.tool_in_spindle) >= 0: old_tool_in_tray= True
            if self.atc.lookup_slot(tool_num) >= 0: new_tool_in_tray = True

            if old_tool_in_tray and new_tool_in_tray:
                message = 'Use    ATC    to    change    tools?'

            elif old_tool_in_tray and not new_tool_in_tray:
                message = 'Use    ATC    to    store    tool?'

            elif not old_tool_in_tray and new_tool_in_tray:
                message = 'Use    ATC    to    fetch    tool?'

            if old_tool_in_tray or new_tool_in_tray:
                dialog = tormach_file_util.yes_no_cancel_popup(message)
                dialog.run()
                no_yes_cancel_response = dialog.response
                dialog.destroy()
                if no_yes_cancel_response == gtk.RESPONSE_YES :
                    invoke_atc = True
                if no_yes_cancel_response == gtk.RESPONSE_CANCEL:
                    return

        if invoke_atc:
            self.dro_list['atc_auto_dro'].set_text(str(tool_num))
            self.dro_list['atc_auto_dro'].queue_draw()
            self.atc.fetch(self.dro_list['atc_auto_dro'])
            return    #we are finally done with ATC crap -

        # Nothing to do with ATC -  Just make the requested tool active with offset
        tool_change_command = 'M61 Q%d G43 H%d' % (tool_num, tool_num)
        self.issue_mdi(tool_change_command)
        self.issue_mdi(tool_change_command)   # do it twice due to bug in Q0

        self.set_image('m6_g43_image', 'M6_G43.png')
        self.window.set_focus(None)

    def on_m6_g43_key_press_event(self, widget, event):
        if event.keyval == gtk.keysyms.Return or event.keyval == 65421:
            self.on_m6_g43_button_release_event(self, widget)
        elif event.keyval == gtk.keysyms.Escape:
            self.set_image('m6_g43_image', 'M6_G43.png')
            self.window.set_focus(None)
        return True


    def stop_all_jogging(self):
        self.ensure_mode(linuxcnc.MODE_MANUAL)
        for jog_axis in range(4):
            self.stop_jog(jog_axis)

    def stop_jog(self, jog_axis):
        # unconditionally stop jog - do not check mode here!!!
        self.jogging_stopped = False
        self.command.jog(linuxcnc.JOG_STOP, jog_axis)

    def get_jog_increment(self, axis_ind):
        """Return a jog increment based on the specified axis index"""
        jog_increment = self.jog_increment
        if self.g21 and self.jog_increment == 0.0001:
            # the 0.001 mm is too small to be useful so bump it up to 0.0025 mm
            jog_increment = jog_increment * 2.5

        return jog_increment * ( self.jog_metric_scalar if axis_ind < 3 else 1.0)

    def jog(self, jog_axis, jog_direction, jog_speed, apply_pct_override=True, jog_mode = None):
        if self.program_running(True):
            return
        if self.status.task_state == linuxcnc.STATE_ESTOP or \
           self.status.task_state == linuxcnc.STATE_ESTOP_RESET or \
           self.status.task_state == linuxcnc.STATE_OFF:
            self.error_handler.write("Must take machine out of estop before jogging")
            return
        # If an explicit jog mode is specified, use that, otherwise assume the
        # current GUI mode
        if jog_mode is None:
            jog_mode = self.jog_mode

        self.ensure_mode(linuxcnc.MODE_MANUAL)


        # Compute actual jog speed from direction, absolute speed, and percent
        # override
        speed = jog_direction * jog_speed
        if apply_pct_override:
            speed *= self.jog_override_pct

        if jog_mode == linuxcnc.JOG_CONTINUOUS:
            #Continous jogging
            self.command.jog(jog_mode, jog_axis, speed)
            self.jogging_stopped = True

        elif jog_mode == linuxcnc.JOG_INCREMENT:
            # Step jogging
            if self.moving(): return

            # Scale distance for the current axis
            displacement = self.get_jog_increment(jog_axis) / self.get_axis_scale(jog_axis)

            self.command.jog(jog_mode,  jog_axis, speed, displacement)


    # ---------------------------------------------------------------------
    # File tab
    # ---------------------------------------------------------------------

    def save_persistent_data(self):
        tool_num = self.status.tool_in_spindle
        self.redis.hset('machine_prefs', 'active_tool', tool_num)
        try:
            for item in self.mdi_history:
                self.redis.rpush('mdi_history', item)
                self.redis.hset('machine_prefs', 'mdi_history_index', self.mdi_history_index)
        except:
            self.error_handler.write("Failed to save MDI history.", ALARM_LEVEL_DEBUG)
            pass

        try:
            # delete old redis values to prevent this list from growing ad infinitum
            self.redis.delete('recent_file_history')
            for row in self.file_history_liststore:
                path = row[1]
                if path != CLEAR_CURRENT_PROGRAM:
                    self.redis.rpush('recent_file_history', path)
        except:
            self.error_handler.write("Failed to save recent file history.", ALARM_LEVEL_DEBUG)
            pass
        if self.f_word != 0: self.redis.hset('machine_prefs', 'feedrate', str(self.f_word))
        if self.s_word != 0: self.redis.hset('machine_prefs', 'spindle_speed', str(self.s_word))



    def on_exit_button_release_event(self, widget, data=None):
        do_button_release_motion(widget)
        self.stop_motion_safely()

        conf_dialog = tormach_file_util.shutdown_confirmation_popup()
        self.window.set_sensitive(False)
        conf_dialog.run()
        response = conf_dialog.response
        if response == gtk.RESPONSE_CANCEL:
            self.window.set_sensitive(True)
            conf_dialog.destroy()
            return
        else:
            conf_dialog.destroy()

        self.quit()

    def quit(self):
        self.save_persistent_data()
        self.atc.process_queue.put(('terminate',None))  #shut down worker bee
        if self.notify_at_cycle_start:  # is anyone waiting on us
            self.notify_at_cycle_start = False
            try:
                self.redis.hset("TormachAnswers",self.notify_answer_key,"!")  #start pressed message
                self.hal['prompt-reply'] = 2
                print ('prompt output pin set to 2 by exit')
            except Exception as e:
                print "Whooops! - Tormach message reply not set", e
        self._quit()
        gtk.main_quit()

    def on_probe_sim_button_press(self, widget, data=None):
        if 'lo' in widget.get_label():
            self.hal['probe-sim'] = 1
            widget.set_label("Probe - hi")
        else:
            self.hal['probe-sim'] = 0
            widget.set_label("Probe - lo")


    # ---------------------------------------------------------------------
    # ATC tab
    #----------------------------------------------------------------------


    # Bob - all callbacks for the buttons on the atc tab are defined on the following lines.  You can ignore the button press events - its
    # just the release events that you're going to be concerned with.

    def on_atc_manual_insert_dro_activate(self, widget, data=None):
        if self.program_running(): return

        valid, value, error_msg = self.conversational.validate_tool_number(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text("%1d" % value)
        self.set_image('atc_insert_image', 'ATC_Insert_Highlighted.png')
        self.button_list['atc_insert'].grab_focus()

    def on_atc_insert_key_press_event(self, widget, event):
        if self.program_running(): return
        if event.keyval == gtk.keysyms.Return or event.keyval == 65421:
            self.on_atc_insert_button_release_event(self.button_list['atc_insert'])
        elif event.keyval == gtk.keysyms.Escape:
            self.set_image('atc_insert_image', 'ATC_Insert.png')
            self.window.set_focus(None)
        return True

    def on_atc_insert_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.set_image('atc_insert_image', 'ATC_Insert.png')
        self.atc.insert(self.dro_list['atc_manual_insert_dro'])

    def on_atc_delete_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.delete(self.dro_list['atc_manual_insert_dro'])

    def on_atc_delete_all_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        if self.program_running(): return
        self.atc.delete_all()

    def on_atc_tray_forward_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        while gtk.events_pending():
            gtk.main_iteration()
        self.atc.tray_fwd()

    def on_atc_tray_reverse_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        while gtk.events_pending():
            gtk.main_iteration()
        self.atc.tray_rev()

    def on_atc_goto_tray_load_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.go_to_tray_load_position()

    def on_atc_retract_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        while gtk.events_pending():
            gtk.main_iteration()
        self.atc.retract()

    def on_atc_drawbar_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        while gtk.events_pending():
            gtk.main_iteration()
        if  self.atc.get_drawbar_state():
            self.atc.set_drawbar_up()
            self.set_image('atc_drawbar_image', 'Drawbar-Down-Green.png')
        else:
            self.atc.set_drawbar_down()
            self.set_image('atc_drawbar_image', 'Drawbar-Up-Green.png')

    def on_atc_blast_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        while gtk.events_pending():
            gtk.main_iteration()
        self.atc.blast()

    def on_atc_ref_tray_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.home_tray ()

    def on_atc_minus_minus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.offset_tray_neg ()

    def on_atc_plus_plus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.offset_tray_pos()

    def on_atc_set_tc_z_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        message = 'Set    tool    change    position   to   z  %.4f?' % (self.status.actual_position[2] * self.get_axis_scale(2))
        dialog = tormach_file_util.ok_cancel_popup(message)
        dialog.run()
        ok_cancel_response = dialog.response
        dialog.destroy()
        if ok_cancel_response == gtk.RESPONSE_OK :
            if self.atc.set_tc_z():
                self.set_image('set_tool_change_z_image', 'Set-TC-POS-Green.png')


    def on_atc_auto_dro_activate(self, widget, data=None):
        if self.program_running(): return
        valid, value, error_msg = self.conversational.validate_tool_number(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text("%1d" % value)
        self.set_image('atc_remove_image', 'ATC_Remove_Highlighted.png')
        self.button_list['atc_remove'].grab_focus()

    def on_atc_remove_key_press_event(self, widget, event):
        if self.program_running(): return
        if event.keyval == gtk.keysyms.Return or event.keyval == 65421:
            self.on_atc_remove_button_release_event(self.button_list['atc_remove'])
        elif event.keyval == gtk.keysyms.Escape:
            self.set_image('atc_remove_image', 'ATC_Remove.png')
            self.window.set_focus(None)
        return True

    def on_atc_remove_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.remove(self.dro_list['atc_auto_dro'])
        self.set_image('atc_remove_image', 'ATC_Remove.png')

    def on_atc_rev_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.atc_rev()

    def on_atc_fw_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.atc_fwd()

    def on_atc_store_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.store()

    def on_atc_touch_entire_tray_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.touch_entire_tray(self.ets_height)


    # ---------------------------------------------------------------------
    # Injection molder tab
    #----------------------------------------------------------------------

    def on_inject_dwell_dro_activate(self, widget, data=None):
        valid, value, error_msg = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        self.injector_dwell = value
        self.redis.hset('machine_prefs', 'injector_dwell', str(self.injector_dwell))
        widget.set_text(self.dro_medium_format % value)
        self.window.set_focus(None)

    def on_inject_button_release_event(self, widget, data=None):
        do_button_release_motion(widget)
        limit = self.status.axis[2]['min_position_limit']
        self.issue_mdi('o<inject> call [%f] [%f] [%f]' % (self.f_word, self.injector_dwell, limit))



    # ---------------------------------------------------------------------
    # settings tab
    #----------------------------------------------------------------------

    def on_enable_soft_keyboard_checkbutton_toggled(self, widget, data=None):
        self.touchscreen_enabled = widget.get_active()
        # change fileview objects flag so that the right click menu obeys the current touchscreen setting,
        # not the setting used when the objects were created.
        if not self.first_run:
            self.hd_file_chooser.touchscreen_enabled = self.touchscreen_enabled
            self.usb_file_chooser.touchscreen_enabled = self.touchscreen_enabled
        self.redis.hset('machine_prefs', 'touchscreen', self.touchscreen_enabled)
        self.window.set_focus(None)

    def on_enable_scanner_checkbutton_toggled(self, widget, data=None):
        #Note: if scanner2 fails to load, then scanner won't enable here
        self.scanner_enabled = widget.get_active()
        self.redis.hset('machine_prefs', 'scanner_enabled', self.scanner_enabled)
        page = self.notebook.get_nth_page(CNC_SCANNER_PAGE)
        if self.scanner_enabled:
            page.show()
            if self.scanner == None:
                self.scanner = scanner2.Scanner(self.status, render_target=self.scanner_common_camera_image)
        else:
            page.hide()
        self.window.set_focus(None)

    def on_enable_injector_checkbutton_toggled(self, widget, data=None):
        self.injector_enabled = widget.get_active()
        self.redis.hset('machine_prefs', 'injector_enabled', self.injector_enabled)
        page = self.notebook.get_nth_page(INJECTOR_PAGE)
        if self.injector_enabled:
            page.show()
        else:
            page.hide()
        self.window.set_focus(None)


    def on_enable_door_sw_checkbutton_toggled(self, widget, data=None):
        self.door_sw_enabled = widget.get_active()
        self.hal['enc-door-switch-configured'] = self.door_sw_enabled
        if self.door_sw_enabled and (self.redis.hget('machine_prefs', 'door_sw_enabled') == 'False'):
            # we've just gone from disabled to enabled, so show a warning next time we ref x
            self.redis.hset('machine_prefs', 'display_door_sw_x_ref_warning', 'True')
        self.redis.hset('machine_prefs', 'door_sw_enabled', self.door_sw_enabled)
        self.window.set_focus(None)
        self.show_or_hide_x_limit_led()
        self.show_or_hide_door_sw_led()

    def show_or_hide_x_limit_led(self):
        if self.door_sw_enabled:
            # hide X limit LED on status screen, change label for Y to show the two are netted together
            self.builder.get_object('x_limit_led').hide()
            self.builder.get_object('x_limit_text').hide()
            self.builder.get_object('y_limit_text').set_markup('<span weight="light" font_desc="Bebas 12" font_stretch="ultracondensed" foreground="white" >x/y   limit:</span>')
        else:
            self.builder.get_object('x_limit_led').show()
            self.builder.get_object('x_limit_text').show()
            self.builder.get_object('y_limit_text').set_markup('<span weight="light" font_desc="Bebas 12" font_stretch="ultracondensed" foreground="white" >y   limit:</span>')

    def show_or_hide_door_sw_led(self):
        if self.door_sw_enabled:
            self.image_list['door_sw_led'].show()
            self.builder.get_object('door_sw_text').show()
        else:
            self.image_list['door_sw_led'].hide()
            self.builder.get_object('door_sw_text').hide()


    def on_g30m998_move_z_only_checkbutton_toggled(self, widget, data=None):
        self.g30m998_move_z_only = widget.get_active()
        self.redis.hset('machine_prefs', 'g30m998_move_z_only', self.g30m998_move_z_only)
        self.window.set_focus(None)

    # these two radio buttons are a group
    def on_passive_probe_radiobutton_toggled(self, widget, data=None):
        if widget.get_active():
            self.probe_active_high = False
            self.redis.hset('machine_prefs', 'probe_active_high', self.probe_active_high)
            self.hal['probe-active-high'] = self.probe_active_high
            self.window.set_focus(None)

    def on_active_probe_radiobutton_toggled(self, widget, data=None):
        if widget.get_active():
            self.probe_active_high = True
            self.redis.hset('machine_prefs', 'probe_active_high', self.probe_active_high)
            self.hal['probe-active-high'] = self.probe_active_high
            self.window.set_focus(None)

    def on_fourth_axis_homing_checkbutton_toggled(self, widget, data=None):
        self.fourth_axis_homing_enabled = widget.get_active()
        self.set_4th_axis_homing_parameters(self.fourth_axis_homing_enabled)
        self.redis.hset('machine_prefs', 'fourth_axis_homing_enabled', self.fourth_axis_homing_enabled)
        self.window.set_focus(None)

    def on_use_atc_checkbutton_toggled(self, widget, data=None):
        if (widget.get_active() and not self.spindle_type == SPINDLE_TYPE_HISPEED):
            page = self.notebook.get_nth_page(ATC_PAGE)
            page.show()
            if not self.is_sim_config:
                self.atc.enable()
                self.only_one_cable_warning == True  #re-notify bad  cable connections
            self.button_list['atc_fwd'].show()
            self.button_list['atc_fwd'].set_sensitive(True)
            self.show_atc_diagnostics()

        elif(widget.get_active() and self.spindle_type == SPINDLE_TYPE_HISPEED):
            self.checkbutton_list['use_manual_toolchange_checkbutton'].set_active(True)
            self.error_handler.write('Cannot use high speed spindle and ATC. Disabling ATC.')

    def on_use_manual_toolchange_checkbutton_toggled(self, widget, data=None):
        if widget.get_active():
            page = self.notebook.get_nth_page(ATC_PAGE)
            page.hide()
            self.atc.disable()
            self.button_list['atc_fwd'].hide()
            self.button_list['atc_fwd'].set_sensitive(False)
            self.hide_atc_diagnostics()


    def on_switch_to_lathe_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.switch_to_lathe()

    # ---------------------------------------------------------------------
    # tool touch off tab
    #----------------------------------------------------------------------
    # on paging to the tool touch we should check the tool type for the currently loaded tool.  If the tool type is 0 (not yet configured)
    # then we display the spash screen.  Also, we need to offer a "reset tool" button that changes the type to 0 and displays the splash.




    # tool_touch page select callback
    def on_notebook_switch_page(self, notebook, page, page_num):
        TormachUIBase.on_notebook_switch_page(self,notebook, page, page_num)

        # log new page - can't do it in ui_common because lathe has different tabs/pages
        if page_num == MAIN_PAGE:
            page_name = 'MAIN_PAGE'
        elif page_num == FILE_PAGE:
            page_name = 'FILE_PAGE'
        elif page_num == SETTINGS_PAGE:
            page_name = 'SETTINGS_PAGE'
        elif page_num == OFFSETS_PAGE:
            page_name = 'OFFSETS_PAGE'
        elif page_num == CONVERSATIONAL_PAGE:
            page_name = 'CONVERSATIONAL_PAGE'
        elif page_num == PROBE_PAGE:
            page_name = 'PROBE_PAGE'
        elif page_num == ATC_PAGE:
            page_name = 'ATC_PAGE'
        elif page_num == CNC_SCANNER_PAGE:
            page_name = 'CNC_SCANNER_PAGE'
        elif page_num == INJECTOR_PAGE:
            page_name = 'INJECTOR_PAGE'
        elif page_num == MILL_STATUS_PAGE:
            page_name = 'MILL_STATUS_PAGE'
        else:
            page_name = 'UNKNOWN PAGE %d' % page_num
        self.error_handler.write('Switched to notebook page: ' + page_name, ALARM_LEVEL_DEBUG)

        if notebook.get_current_page() == CONVERSATIONAL_PAGE:
            self.save_title_dro()
        if page_num != MILL_STATUS_PAGE:
            # we're leaving the alarm page, so clear interp_alarm and conv_param_alarm flags as we've already seen the alarm
            # and this is the only mechanism for "clearing" these alarms.
            # the estop alarm is ONLY cleared on RESET button press.
            self.interp_alarm = False
            self.error_handler.clear()

        else:
            # switching to Status tab
            # hide/unhide USB I/O Interface
            if not self.usbio_enabled:
                self.hide_usbio_interface()

            if self.atc.operational:
                self.show_atc_diagnostics()
            else:
                self.hide_atc_diagnostics()

        if page_num == SETTINGS_PAGE:
            # refresh active codes display
            self.gcodes_display.highlight_active_codes(self.active_gcodes())

            # this next call to set the appropriate active state of the scanner checkbutton SHOULD be in init,
            # but for some unknown reason if the argument to set_active was False, the realize event of the
            # notebook would fail to connect to the show_enabled_notebook_tabs method.  This workaround is a band aid
            # for this problem.
            self.checkbutton_list['enable_scanner_checkbutton'].set_sensitive(_scanner_available)
            self.checkbutton_list['enable_scanner_checkbutton'].set_active(self.scanner_enabled)

        if page_num != OFFSETS_PAGE:
            # tell the height gauge HAL comp to go to sleep
            self.hal['hg-enable'] = False

        if page_num == OFFSETS_PAGE:
            self.refresh_tool_liststore()
            self.highlight_offsets_treeview_row()
            # this also should be handled in init, but when these are called from init the gtk widgets haven't yet been realized
            # and the widget visibility isn't set appropriately.  This is another bandaid on this problem
            if self.atc.operational:
                self.show_atc_diagnostics()
                self.button_list['atc_fwd'].show()
                self.button_list['atc_fwd'].set_sensitive(True)
            else:
                self.hide_atc_diagnostics()
                self.button_list['atc_fwd'].hide()
                self.button_list['atc_fwd'].set_sensitive(False)

            # tell the height gauge HAL comp to wake up
            self.hal['hg-enable'] = True
            self.zero_height_gauge_show_or_hide()

            # Be sure the work offsets are updated when switching to
            # the notebook
            self.refresh_work_offset_liststore()

        if page_num == ATC_PAGE:

            if self.moving(): return
            self.atc.display_tray()

        if page_num == CONVERSATIONAL_PAGE:
            self.load_title_dro()

            self.thread_custom_file_reload_if_changed()

            if self.g21:
                unit_string = 'mm'
                self.thread_chart_combobox.set_model(self.thread_chart_g21_liststore)
            else:
                unit_string = 'in'
                self.thread_chart_combobox.set_model(self.thread_chart_g20_liststore)

            html_fmt = '<span weight="light" font_desc="Bebas 12" font_stretch="ultracondensed" foreground="white" >%s:</span>'
            self.tap_labels['tpu'].set_markup(html_fmt % 'Threads/%s      ' % unit_string)
            self.tap_labels['pitch'].set_markup(html_fmt % 'Pitch    (%s)    ' % unit_string)
            self.thread_mill_tpu_label.set_markup(html_fmt %'Threads/%s    ' % unit_string)
            self.thread_mill_pitch_label.set_markup(html_fmt %'Pitch    (%s)    ' % unit_string)
            z_drill_hint_visible = self.conv_notebook.get_current_page() == MILL_DRILL_TAP and self.conv_drill_tap == 'drill'
            if z_drill_hint_visible:
                self.update_drill_z_feed_per_rev_hint()
            self.drill_z_feed_per_rev_hint.set_visible(z_drill_hint_visible)

            self.ef_num_rows = self.setup_font_selector()

    # startup actions for each conversational page, such as graying out DROs
    # that don't apply
    # These need to match the focus passing order in the
    # 'on_conv_???_dro_activate' modules
    def _conversational_notebook_switch_page(self, conv_page_num ):
        # TODO - save off values in common dros in redis, keyed to the page that the user was on.
        # restore these values when the user switches to the new page.
        tap_z_feed = self.calc_tap_z_feed_rate()
        if tap_z_feed != self.current_normal_z_feed_rate:
            self.conv_dro_list['conv_z_feed_dro'].set_text(self.current_normal_z_feed_rate)
        self.save_title_dro()
        self.load_title_dro(conv_page_num)
        self.drill_z_feed_per_rev_hint.set_visible(False)

        if conv_page_num == MILL_FACE:
            self.conv_dro_list['conv_work_offset_dro'].set_sensitive(True)
            self.conv_dro_list['conv_tool_number_dro'].set_sensitive(True)
            self.conv_dro_list['conv_rpm_dro'].set_sensitive(True)
            self.conv_dro_list['conv_feed_dro'].set_sensitive(True)
            self.conv_dro_list['conv_z_feed_dro'].set_sensitive(True)
            self.conv_dro_list['conv_z_clear_dro'].set_sensitive(True)
            self.on_conversational_face_switch_page()

        if conv_page_num == PROFILE:
            self.conv_dro_list['conv_work_offset_dro'].set_sensitive(True)
            self.conv_dro_list['conv_tool_number_dro'].set_sensitive(True)
            self.conv_dro_list['conv_rpm_dro'].set_sensitive(True)
            self.conv_dro_list['conv_feed_dro'].set_sensitive(True)
            self.conv_dro_list['conv_z_feed_dro'].set_sensitive(True)
            self.conv_dro_list['conv_z_clear_dro'].set_sensitive(True)

        if conv_page_num == POCKET:
            self.conv_dro_list['conv_work_offset_dro'].set_sensitive(True)
            self.conv_dro_list['conv_tool_number_dro'].set_sensitive(True)
            if self.conv_pocket_rect_circ == 'rect':
                self.conv_dro_list['conv_rpm_dro'].set_sensitive(True)
                self.conv_dro_list['conv_feed_dro'].set_sensitive(True)
                self.conv_dro_list['conv_z_feed_dro'].set_sensitive(True)
            else:  # self.conv_pocket_rect_circ == 'circ':
                self.conv_dro_list['conv_rpm_dro'].set_sensitive(True)
                self.conv_dro_list['conv_feed_dro'].set_sensitive(True)
                self.conv_dro_list['conv_z_feed_dro'].set_sensitive(True)
            self.conv_dro_list['conv_z_clear_dro'].set_sensitive(True)

        if conv_page_num == MILL_DRILL_TAP:  # Drill/Tap button should also set these
            self.conv_dro_list['conv_work_offset_dro'].set_sensitive(True)
            self.conv_dro_list['conv_tool_number_dro'].set_sensitive(True)
            self.update_drill_through_hole_hint()
            if self.conv_drill_tap == 'drill':
                self.drill_z_feed_per_rev_hint.set_visible(True)
                self.conv_dro_list['conv_rpm_dro'].set_sensitive(True)
                self.conv_dro_list['conv_feed_dro'].set_sensitive(False)
                self.conv_dro_list['conv_z_feed_dro'].set_sensitive(True)
                self.update_drill_z_feed_per_rev_hint()
            else:   # self.conv_drill_tap == 'tap':
                tap_z_feed = self.calc_tap_z_feed_rate()
                self.conv_dro_list['conv_z_feed_dro'].set_text(tap_z_feed)
                self.conv_dro_list['conv_rpm_dro'].set_sensitive(True)
                self.conv_dro_list['conv_feed_dro'].set_sensitive(False)
                self.conv_dro_list['conv_z_feed_dro'].set_sensitive(False)
            self.conv_dro_list['conv_z_clear_dro'].set_sensitive(True)

        if conv_page_num == THREAD_MILL:
            self.conv_dro_list['conv_work_offset_dro'].set_sensitive(True)
            self.conv_dro_list['conv_tool_number_dro'].set_sensitive(True)
            self.conv_dro_list['conv_rpm_dro'].set_sensitive(True)
            self.conv_dro_list['conv_feed_dro'].set_sensitive(True)
            self.conv_dro_list['conv_z_feed_dro'].set_sensitive(False)
            self.conv_dro_list['conv_z_clear_dro'].set_sensitive(True)

        if conv_page_num == ENGRAVE_TEXT:
            self.conv_dro_list['conv_work_offset_dro'].set_sensitive(True)
            self.conv_dro_list['conv_tool_number_dro'].set_sensitive(True)
            self.conv_dro_list['conv_rpm_dro'].set_sensitive(True)
            self.conv_dro_list['conv_feed_dro'].set_sensitive(True)
            self.conv_dro_list['conv_z_feed_dro'].set_sensitive(False)
            self.conv_dro_list['conv_z_clear_dro'].set_sensitive(True)
            self.conv_engrave_switch_page()

        if conv_page_num == JOB_ASSIGNMENT:
            #self.conv_dro_list['conv_title_dro',].set_sensitive(True)
            self.conv_dro_list['conv_work_offset_dro'].set_sensitive(False)
            self.conv_dro_list['conv_tool_number_dro'].set_sensitive(False)
            self.conv_dro_list['conv_rpm_dro'].set_sensitive(False)
            self.conv_dro_list['conv_feed_dro'].set_sensitive(False)
            self.conv_dro_list['conv_z_feed_dro'].set_sensitive(False)
            self.conv_dro_list['conv_z_clear_dro'].set_sensitive(False)

    def on_conversational_notebook_switch_page(self, notebook, page, conv_page_num ):
        self._conversational_notebook_switch_page(conv_page_num)

    def on_set_g30_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.set_image('set_g30_image', 'set_g30_green_led.png')
        # store current position in parameters 5161, 5163
        self.issue_mdi('g30.1')
        # when going to tc position, we'll need to remap G28 so that it calls G28 X#5420 - parameter 5420 stores current X position
        # so that a move to TC pos is performed in Z first.

    def on_goto_g30_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # hold X constant so that machine moves in Z only
        self.issue_mdi('g30 Z#5422')

    def on_touch_z_dro_activate(self, widget, data=None):

        valid, dro_val, error_msg = self.conversational.validate_z_point(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        self.dro_list['touch_z_dro'].set_text(self.dro_long_format % dro_val)
        self.set_image('touch_z_image', 'touch_z_highlight.png')
        # next line not working as it should.
        self.button_list['touch_z'].grab_focus()

    def on_touch_z_button_release_event(self, widget, data=None):
        self.tool_offsets_fixed.move(self.button_list['touch_z'], self.button_list['touch_z'].x, self.button_list['touch_z'].y)

        valid, dro_val, error_msg = self.conversational.validate_z_touch_val(self.dro_list['touch_z_dro'])
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        ind = 2
        # the G10 command wants values in mm if G21, but actual_postion and g5x_offsets are in machine units (in.)
        # so we take the sup value and turn it into machine units, then send the offset command in g20/21 units
        supplemental_offset = dro_val / self.get_axis_scale(ind)
        tool_number = self.status.tool_in_spindle
        # g10 doesn't like tool number = zero, and tool number will be -1 in some cases on startup
        if tool_number < 1:
            self.error_handler.write('Cannot set tool offset for tool zero.  Please enter a valid tool number in the tool DRO before using Touch Z button', ALARM_LEVEL_MEDIUM)
            return

        z_offset = self.status.actual_position[ind] - self.status.g5x_offset[ind] - supplemental_offset
        z_offset = z_offset * self.get_axis_scale(ind)

        # can't use self.issue_tool_offset_command() here as this takes L10, other calls take L1
        g10_command = "G10 L10 P%d Z%f" %(tool_number, dro_val)
        self.issue_mdi(g10_command)
        self.command.wait_complete()
        self.issue_mdi("G43")
        self.dro_list['touch_z_dro'].set_text(self.dro_long_format % dro_val)
        self.set_image('touch_z_image', 'touch_z_green_led.png')
        self.window.set_focus(None)
        # kludge for asyncronous refresh of tool table, handled in periodic
        self.tool_liststore_stale = 2


    def on_touch_z_key_press_event(self, widget, event):
        # Return or Enter key valid.  couldn't find keysyms constant for Enter key.
        if event.keyval == gtk.keysyms.Return or event.keyval == 65421:
            self.on_touch_z_button_release_event(self, self.button_list['touch_z'])
            self.window.set_focus(None)
        elif event.keyval == gtk.keysyms.Escape:
            self.set_image('touch_z_image', 'touch_z_black_led.png')
            self.window.set_focus(None)
        return True

    def on_move_and_set_tool_length_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        if self.status.tool_in_spindle < 1:
            self.error_handler.write("Cannot set tool length with tool 0 in spindle.  Please change the active tool to a valid tool number before proceeding.", ALARM_LEVEL_MEDIUM)
            return
        # set flag used by periodic to refresh tool treeview
        self.tool_liststore_stale = 2
        probing.move_and_set_tool_length(self)


    def on_move_and_set_work_offset_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        if self.ets_height < 0:
            self.error_handler.write('Set tool setter (Probe/ETS Setup, Step 2) before tool length', ALARM_LEVEL_LOW)
            return
        self.work_probe_in_progress = True
        probing.find_work_z_with_ets(self)

    def on_atc_fwd_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.atc.atc_fwd()
        #print self.current_tool_z_offset.zoffset

    # ~~~~~~~~~
    # tool table callbacks
    # ~~~~~~~~~
    def tool_table_update_focus(self,row,column,start_editing):
        """Wrapper for set_cursor"""
        self.treeview.set_cursor(row, column, start_editing)
        self.tt_scroll_adjust(row)

    def tt_scroll_adjust(self, row):
        # get var list from vertical scroll bar
        adj = self.scrolled_window_tool_table.get_vadjustment()
        #print "--kw dt v_adj   lower =", adj.lower, "   upper =", adj.upper, "   page size =", adj.page_size, "   value =", adj.value

        unitsperrow = (adj.upper - adj.lower) / TOOL_TABLE_ROWS
        centerofpage = adj.page_size / 2
        centerofrow = unitsperrow / 2
        cofcurrentrow = (row * unitsperrow) + centerofrow
        scroll_offset = cofcurrentrow - centerofpage

        if scroll_offset < 0:
            scroll_offset = 0
        elif scroll_offset > (adj.upper - adj.page_size):
            scroll_offset = (adj.upper - adj.page_size)

        #print "--kw scroll_adjust =", scroll_offset

        adj.set_value(scroll_offset)

    # ~~~~~~~~~  tool_description_column handlers
    def on_tool_description_column_editing_started(self, desc_renderer, editable, path):
        # upon entering this cell, capture the context and setup what to do and where to go next
        #editable.modify_font(drill_font)  # reassert any previous font change to this next editing context
        if path == '':
            row = 0
        else:
            row = int(path)
        # capture key press to determine next cell to edit
        editable.connect("key-press-event",self.on_tool_description_column_keypress,row)

    def on_tool_description_column_keypress(self,widget,ev,row):
        if ev.keyval == gtk.keysyms.Return:
            # a Return in this column moves the cursor to the next column
            # editing is started in the new location
            glib.idle_add(self.tool_table_update_focus, row, self.tool_diameter_column, True)
        return False

    def on_tool_description_column_edited(self, cell, row, tool_description, model ):
        pocket = int(row) + 1
        tool_number = self.status.tool_table[pocket].id
        s = tool_description
        s1 = s.replace('(','[')
        s2 = s1.replace(')',']')
        model[row][1] = s2
        self.redis.hset('tool_descriptions', str(tool_number), s2)


    # ~~~~~~~~~  tool_diameter_column handlers
    def on_tool_diameter_column_editing_started(self, diam_renderer, editable, path):
        # upon entering this cell, capture the context and setup what to do and where to go next
        #editable.modify_font(drill_font)  # reassert any previous font change to this next editing context
        if path == '':
            row = 0
        else:
            row = int(path)
        # capture key press to determine next cell to edit
        editable.connect("key-press-event",self.on_tool_diameter_column_keypress,row)

    def on_tool_diameter_column_keypress(self,widget,ev,row):
        if ev.keyval == gtk.keysyms.Return:
            glib.idle_add(self.tool_table_update_focus, row, self.tool_length_column, True)
        return False

    def on_tool_diameter_column_edited(self, cell, row, value, model ):
        # support for user deleteing old value, not entering 0.0
        if value is '': value = '0.0'
        valid, value, error_msg = self.conversational.validate_tool_offset(value)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        pocket = int(row) + 1
        tool_number = self.status.tool_table[pocket].id
        self.issue_tool_offset_command('R', tool_number, (value/2))
        model[row][2] = "%0.4f" % value


    # ~~~~~~~~~  tool_length_column handlers
    def on_tool_length_column_editing_started(self, length_renderer, editable, path):
        # upon entering this cell, capture the context and setup what to do and where to go next
        #editable.modify_font(drill_font)  # reassert any previous font change to this next editing context
        if path == '':
            row = 0
        else:
            row = int(path)
        # capture key press to determine next cell to edit
        editable.connect("key-press-event",self.on_tool_length_column_keypress,row)

    def on_tool_length_column_keypress(self,widget,ev,row):
        if ev.keyval == gtk.keysyms.Return:
            glib.idle_add(self.tool_table_update_focus, row + 1, self.tool_description_column, True)
        return False

    def on_tool_length_column_edited(self, cell, row, value, model ):
        # support for user deleteing old value, not entering 0.0
        if value is '': value = '0.0'
        valid, value, error_msg = self.conversational.validate_tool_offset(value)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        pocket = int(row) + 1
        tool_number = self.status.tool_table[pocket].id
        self.issue_tool_offset_command('Z', tool_number, value)
        model[row][3] = "%0.4f" % value
        if tool_number == self.status.tool_in_spindle:
            # wer're changing the length offset, so we want to reapply it as well
            self.command.wait_complete()
            self.issue_mdi("G43")



    # -------------------------------------------------------------------------------------------------
    # end of tool touch-off callbacks
    # -------------------------------------------------------------------------------------------------

    # ---------------------------------------------------------------------
    # work offset tab callbacks
    # ---------------------------------------------------------------------

    def on_work_column_editing_started(self, renderer, editable, path,
                                         next_col, row_incr):
        if path == '':
            row = 0
        else:
            row = int(path)
        editable.modify_font(self.work_font)
        # capture key press to determine next cell to edit
        editable.connect("key-press-event",self.on_work_column_keypress,row,
                         next_col, row_incr)

    def on_work_column_keypress(self, widget, ev, row, next_col, row_incr):
        if ev.keyval == gtk.keysyms.Return:
            glib.idle_add(self.work_treeview.set_cursor,
                          row+row_incr, next_col, True)
        return False

    def on_work_column_edited(self, cell, row, value, model, axis ):
        if value == '':  value = '0.0'
        valid, value, error_msg = self.conversational.validate_offset(
            value, axis.upper())
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        row = 0 if row == '' else int(row)
        col = dict(x=1,y=2,z=3,a=4)[axis]
        model[row][col] = ("%0.4f" % value) if isinstance(value,float) else value
 
        g10_command = "G10 L2 P%s %s%s" % (int(row)+1, axis.upper(), value)
        self.issue_mdi(g10_command)
        self.command.wait_complete()

    # ---------------------------------------------------------------------
    # end of work offset tab callbacks
    # ---------------------------------------------------------------------



    # -------------------------------------------------------------------------------------------------
    # conversational tab callbacks
    # -------------------------------------------------------------------------------------------------

    def onThreadTab(self):
        if self.conv_notebook.get_current_page() == THREAD_MILL:
            return True
        return False

    def generate_gcode(self, tab_text=None):
        active_child = self.conv_notebook.get_nth_page(self.conv_notebook.get_current_page())
        active_tab_text = self.conv_notebook.get_tab_label_text(active_child) if tab_text is None else tab_text
        valid = False

        if active_tab_text == "Face":
            (valid, gcode_output_list) = self.conversational.generate_face_gcode(self.conv_dro_list, self.face_dro_list, self.conv_face_spiral_rect)
            self.save_conv_parameters(self.face_dro_list)

        if active_tab_text == "Profile":
            (valid, gcode_output_list) = self.conversational.generate_profile_gcode(self.conv_dro_list, self.profile_dro_list, self.conv_profile_rect_circ)
            self.save_conv_parameters(self.profile_dro_list)

        if active_tab_text == "Pocket":
            if self.conv_pocket_rect_circ == 'rect':
                (valid, gcode_output_list) = self.conversational.generate_pocket_rect_gcode(self.conv_dro_list, self.pocket_rect_dro_list)
                self.save_conv_parameters(self.pocket_rect_dro_list)
            else: # Pocket, Circular
                # X Y locations are from the drill table, so check table
                # find last row
                last_row = 0
                row_id = 0
                for row in self.drill_liststore:
                    if (row[1] != '') or (row[2] != ''):  # something is in this row
                        last_row = row_id
                    row_id += 1

                # check for valid table entries
                # TODO - This is called a number of times near here, so maybe make a function and call it?
                # TODO - The error text is the only difference
                id_cnt = 0
                for row in self.drill_liststore:
                    if id_cnt <= last_row:
                        if (row[1] == '') and (row[2] == ''):  # empty row
                            # highlight X and Y
                            row[1] = '??'
                            row[2] = '??'
                        elif row[1] == '':  # something is in Y
                            # highlight X
                            row[1] = '??'
                        elif row[2] == '':  # something is in X
                            # highlight Y
                            row[2] = '??'
                    id_cnt += 1

                for row in self.drill_liststore:
                    if (row[1] == '??') or (row[2] == '??'):  # errors exist in table
                        self.error_handler.write('Pocket, Circular - Please fill in X Y locations in the Drill table, then return to Pocket, Circular and Post')
                        self.conv_notebook.set_current_page(MILL_DRILL_TAP)
                        return False, ''

                (valid, gcode_output_list) = self.conversational.generate_pocket_circ_gcode(self.conv_dro_list, self.pocket_circ_dro_list, self.drill_liststore)
                self.save_conv_parameters(self.pocket_circ_dro_list)

        if "Drill" in active_tab_text:
            if self.drill_pattern_notebook_page == 'pattern':
                # find last row
                last_row = 0
                row_id = 0
                for row in self.drill_liststore:
                    if (row[1] != '') or (row[2] != ''):  # something is in this row
                        last_row = row_id
                    row_id += 1
                 # check for valid table entries
                id_cnt = 0
                for row in self.drill_liststore:
                    if id_cnt <= last_row:
                        if (row[1] == '') and (row[2] == ''):  # empty row
                            # highlight X and Y
                            row[1] = '??'
                            row[2] = '??'
                        elif row[1] == '':  # something is in Y
                            # highlight X
                            row[1] = '??'
                        elif row[2] == '':  # something is in X
                            # highlight Y
                            row[2] = '??'
                    id_cnt += 1

                for row in self.drill_liststore:
                    if (row[1] == '??') or (row[2] == '??'):  # errors exist in table
                        return False, ''

            if self.conv_drill_tap == "drill":
                (valid, gcode_output_list) = self.conversational.generate_drill_gcode(self.conv_dro_list, self.drill_dro_list, self.drill_circular_dro_list, self.drill_pattern_notebook_page, self.drill_liststore)
                self.save_conv_parameters(self.drill_dro_list)
                self.save_conv_parameters(self.drill_circular_dro_list)
            else:  # == tap
                (valid, gcode_output_list) = self.conversational.generate_tap_gcode(self.conv_dro_list, self.tap_dro_list, self.drill_circular_dro_list, self.drill_pattern_notebook_page, self.drill_liststore, self.tap_2x_enabled)
                self.save_conv_parameters(self.tap_dro_list)
                self.save_conv_parameters(self.drill_circular_dro_list)

        if active_tab_text == "Thread Mill":

            # find last row
            last_row = 0
            row_id = 0
            for row in self.drill_liststore:
                if (row[1] != '') or (row[2] != ''):  # something is in this row
                    last_row = row_id
                row_id += 1

            # check for valid table entries
            id_cnt = 0
            for row in self.drill_liststore:
                if id_cnt <= last_row:
                    if (row[1] == '') and (row[2] == ''):  # empty row
                        # highlight X and Y
                        row[1] = '??'
                        row[2] = '??'
                    elif row[1] == '':  # something is in Y
                        # highlight X
                        row[1] = '??'
                    elif row[2] == '':  # something is in X
                        # highlight Y
                        row[2] = '??'
                id_cnt += 1

            for row in self.drill_liststore:
                if (row[1] == '??') or (row[2] == '??'):  # errors exist in table
                    if self.current_notebook_page == THREAD_MILL:
                        self.error_handler.write('Thread Mill - Please fill in X Y locations in the Drill table, then return to Thread Mill and Post')
                        self.conv_notebook.set_current_page(MILL_DRILL_TAP)
                    return False, ''

            if self.conv_thread_mill_ext_int == 'external':
                (valid, gcode_output_list) = self.conversational.generate_thread_mill_ext_gcode(self.conv_dro_list, self.thread_mill_ext_dro_list, self.drill_liststore, self.thread_mill_rhlh)
                self.save_conv_parameters(self.thread_mill_ext_dro_list)
            else:
                (valid, gcode_output_list) = self.conversational.generate_thread_mill_int_gcode(self.conv_dro_list, self.thread_mill_int_dro_list, self.drill_liststore, self.thread_mill_rhlh)
                self.save_conv_parameters(self.thread_mill_int_dro_list)

        if active_tab_text == "Engrave":
            if self.engrave_font_pf == '':  # TODO: this may have been done elsewhere?
                self.error_handler.write('Engrave error - Please select a font')
                gcode_output_list = ''
            else:
                (valid, gcode_output_list) = self.conversational.generate_engrave_gcode(self.conv_dro_list, self.engrave_dro_list, self.engrave_font_pf, self.engrave_just)
                self.save_conv_parameters(self.engrave_dro_list)

        active_main_child = self.notebook.get_nth_page(self.notebook.get_current_page())
        #print "--kw active_main_child =", active_main_child
        active_main_tab_text = self.notebook.get_tab_label_text(active_main_child)
        #print "--kw active_main_tab_text = ", active_main_tab_text

        active_camera_child = self.camera_notebook.get_nth_page(self.camera_notebook.get_current_page())
        #print "--kw active_camera_child =", active_camera_child
        active_camera_tab_text = self.camera_notebook.get_tab_label_text(active_camera_child)
        #print "--kw active_camera_tab_text = ", active_camera_tab_text

        if active_main_tab_text == 'Camera' and active_camera_tab_text == 'Scope':
            (valid, gcode_output_list) = self.conversational.generate_scope_gcode(self.scope_liststore)
            self.save_conv_parameters(self.face_dro_list)

        return valid, gcode_output_list

    def on_post_to_file_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return

        # generate the code
        valid, gcode_output_list = self.generate_gcode()
        if valid:
            self.save_title_dro()
            self.post_to_file(self.conv_dro_list['conv_title_dro'].get_text(), gcode_output_list)

    def on_append_to_file_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return

        # generate the code:
        valid, gcode_output_list = self.generate_gcode()
        if not valid:
            return

        path = self.last_used_save_as_path + os.path.sep
        with tormach_file_util.append_to_file_popup(path, self.touchscreen_enabled) as dialog:
            #Get information from dialog, then destroy automatically
            response = dialog.response
            self.last_used_save_as_path = dialog.current_directory
            path = dialog.get_path()

        if response == gtk.RESPONSE_OK:
            self._update_append_file(path, gcode_output_list)

    #def on_conv_g20_g21_dro_activate(self, widget, data=None):
    #    self.dro_list['conv_work_offset_dro'].grab_focus()
    #    return

    ####  Common DROs, get text and focus passing
    # DRO gray-outs are done in on_conversational_notebook_switch_page
    def on_conv_title_dro_activate(self, widget, data=None):
        self.conv_title = widget.get_text()
        self.conv_dro_list['conv_work_offset_dro'].grab_focus()

    def on_conv_work_offset_dro_activate(self, widget, data=None):
        (valid, work_offset, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(work_offset)
        self.conv_dro_list['conv_tool_number_dro'].grab_focus()
        return

    def _update_stepover_hints(self, tool_number=None):
        if tool_number is None:
            str_num = self.conv_dro_list['conv_tool_number_dro'].get_text()
            try:
                tool_number = int(str_num)
            except:
                return


        tool_dia = self.status.tool_table[tool_number].diameter * self.ttable_conv
        stepover_hint = .7 * tool_dia
        stepover_hint_27 = 0.27 * tool_dia

        self.face_stepover_hint_label.set_markup('<span weight="light" font_desc="Bebas 8" font_stretch="ultracondensed" foreground="white">(.7    *    %s    tool    dia.    =    %s)</span>' % (self.dro_long_format, self.dro_long_format) % (tool_dia, stepover_hint))
        self.profile_stepover_hint_label.set_markup('<span weight="light" font_desc="Bebas 8" font_stretch="ultracondensed" foreground="white">(.27    *    %s    tool    dia.    =    %s)</span>' % (self.dro_long_format, self.dro_long_format) % (tool_dia, stepover_hint_27))
        self.pocket_rect_stepover_hint_label.set_markup('<span weight="light" font_desc="Bebas 8" font_stretch="ultracondensed" foreground="white">(.27    *    %s    tool    dia.    =\n    %s)</span>' % (self.dro_long_format, self.dro_long_format) % (tool_dia, stepover_hint_27))
        return

    def on_conv_tool_number_dro_activate(self, widget, data=None):
        (valid, tool_number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        self.update_drill_through_hole_hint()
        self._update_stepover_hints(tool_number)
        widget.set_text(self.dro_short_format % tool_number)
        self.conv_dro_list['conv_rpm_dro'].grab_focus()

    def on_conv_rpm_dro_activate(self, widget, data=None):
        (valid, rpm, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_short_format % rpm)

        active_child = self.conv_notebook.get_nth_page(self.conv_notebook.get_current_page())
        active_tab_text = self.conv_notebook.get_tab_label_text(active_child)
        next_focus = 'conv_feed_dro'
        if active_tab_text == "Drill / Tap":
            next_focus = 'conv_z_feed_dro'
            if self.conv_drill_tap == 'tap':
                next_focus = 'conv_z_clear_dro'
                try:  # calculate related dwell travel label
                    dwell = float(self.tap_dro_list['tap_dwell_dro'].get_text())
                    pitch = float(self.tap_dro_list['tap_pitch_dro'].get_text())
                    # half_dwell_travel = dwell * rpm * min/60s * pitch * 1/2
                    half_dwell_travel = (dwell * rpm * pitch) / 120
                    self.tap_labels['dwell_travel_calc'].modify_font(self.drill_calc_font)
                    self.tap_labels['dwell_travel_calc'].set_markup('<span foreground="white">%s</span>' % self.dro_dwell_format % half_dwell_travel)
                except:
                    self.tap_labels['dwell_travel_calc'].set_text('')

                self.conv_dro_list['conv_z_feed_dro'].set_text(self.calc_tap_z_feed_rate())
                self.conv_dro_list['conv_z_clear_dro'].grab_focus()
            else: # back to drill
                tap_z_feed = self.calc_tap_z_feed_rate()
                if tap_z_feed != self.current_normal_z_feed_rate:
                    self.conv_dro_list['conv_z_feed_dro'].set_text(self.current_normal_z_feed_rate)
                self.update_drill_z_feed_per_rev_hint()
                self.conv_dro_list['conv_z_feed_dro'].grab_focus()
            return

        else:
            self.conv_dro_list['conv_feed_dro'].grab_focus()
        return

    def on_conv_feed_dro_activate(self, widget, data=None):
        (valid, feed, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_medium_format % feed)

        active_child = self.conv_notebook.get_nth_page(self.conv_notebook.get_current_page())
        active_tab_text = self.conv_notebook.get_tab_label_text(active_child)
        if active_tab_text == "Drill / Tap":
            if self.conv_drill_tap == 'tap':
                # calculate related RPM DRO based on pitch
                # feed is okay so, check if either pitch or tpu are valid, if so calculate the rest of the DROs
                (valid, pitch, error_msg) = self.conversational.validate_param(self.tap_dro_list['tap_pitch_dro'])
                if not valid:  # no pitch, so check for tpu
                    (valid, tpu, error_msg) = self.conversational.validate_param(self.tap_dro_list['tap_tpu_dro'])
                    if not valid:
                        self.tap_dro_list['tap_pitch_dro'].grab_focus()
                    else:  # tpu okay
                        pitch = 1 / tpu
                        self.tap_dro_list["tap_pitch_dro"].set_text(self.dro_long_format % pitch)
                        (valid, pitch, error_msg) = self.conversational.validate_param(self.tap_dro_list['tap_pitch_dro'])
                        rpm = feed / pitch
                        self.conv_dro_list['conv_rpm_dro'].set_text(self.dro_short_format % rpm)

                else:  # pitch is okay
                    tpu = 1 / pitch
                    self.tap_dro_list["tap_tpu_dro"].set_text(self.dro_medium_format % tpu)
                    (valid, tpu, error_msg) = self.conversational.validate_param(self.tap_dro_list['tap_tpu_dro'])
                    rpm = feed / pitch
                    self.conv_dro_list['conv_rpm_dro'].set_text(self.dro_short_format % rpm)
                    self.conv_dro_list['conv_z_clear_dro'].grab_focus()

                dwell = float(self.tap_dro_list['tap_dwell_dro'].get_text())
                pitch = float(self.tap_dro_list['tap_pitch_dro'].get_text())
                # half_dwell_travel = dwell * rpm * min/60s * pitch * 1/2
                half_dwell_travel = (dwell * rpm * pitch) / 120
                self.tap_labels['dwell_travel_calc'].modify_font(self.drill_calc_font)
                self.tap_labels['dwell_travel_calc'].set_markup('<span foreground="white">%s</span>' % self.dro_dwell_format % half_dwell_travel)
            else: #'drill'
                try:  # calculate related Z feed DRO
                    pitch = float(self.tap_dro_list['tap_pitch_dro'].get_text())
                    rpm = float(self.conv_dro_list['conv_rpm_dro'].get_text())
                    z_feed = pitch * rpm
                    tap_z_feed = self.dro_medium_format % z_feed
                    if tap_z_feed != self.current_normal_z_feed_rate:
                        self.conv_dro_list['conv_z_feed_dro'].set_text(self.current_normal_z_feed_rate)
                except:
                    pass

        elif active_tab_text == "Thread Mill" or active_tab_text == "Engrave":
            self.conv_dro_list['conv_z_clear_dro'].grab_focus()
        else:
            self.conv_dro_list['conv_z_feed_dro'].grab_focus()
        return

    def on_conv_z_feed_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_medium_format % value)
        self.update_drill_z_feed_per_rev_hint()
        self.conv_dro_list['conv_z_clear_dro'].grab_focus()
        self.current_normal_z_feed_rate = self.conv_dro_list['conv_z_feed_dro'].get_text()

    def on_conv_z_clear_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        active_child = self.conv_notebook.get_nth_page(self.conv_notebook.get_current_page())
        active_tab_text = self.conv_notebook.get_tab_label_text(active_child)
        if active_tab_text == "Face":
            self.face_dro_list['face_x_start_dro'].grab_focus()
        if active_tab_text == "Profile":
            if self.conv_profile_rect_circ == 'rect':
                self.profile_dro_list['profile_x_prfl_start_dro'].grab_focus()
            else:
                self.profile_dro_list['profile_circ_x_start_dro'].grab_focus()
        if active_tab_text == "Pocket":
            if self.conv_pocket_rect_circ == 'rect':
                self.pocket_rect_dro_list['pocket_rect_x_start_dro'].grab_focus()
            else:  # self.conv_pocket_rect_circ == 'circ':
                self.pocket_circ_dro_list['pocket_circ_diameter_dro'].grab_focus()
        if active_tab_text == "Drill / Tap":
            if self.conv_drill_tap == 'drill':
                self.drill_dro_list['drill_z_start_dro'].grab_focus()
            else:  # self.conv_drill_tap == 'tap'
                self.tap_dro_list['tap_z_end_dro'].grab_focus()
        if active_tab_text == "Thread Mill":
            if self.conv_thread_mill_ext_int == 'internal':
                self.thread_mill_int_dro_list['thread_mill_int_z_start_dro'].grab_focus()
            else:  # self.conv_thread_mill_ext_int == 'external'
                self.thread_mill_ext_dro_list['thread_mill_ext_z_start_dro'].grab_focus()
        if active_tab_text == "Engrave":
            self.engrave_dro_list['engrave_text_dro'].grab_focus()
        return



    # -------------------------------------------------------------------------------------------------
    # Conversational
    # Face DRO handlers
    # -------------------------------------------------------------------------------------------------

    def on_conversational_face_switch_page(self):
        return

    def face_spirial_rect_to_str(self):
        return 'Rectangular' if self.conv_face_spiral_rect == 'rect' else 'Spiral'

    def on_face_spiral_rect_set_state(self):
        # in this case nothing chnages accept style of cutting
        if not self.in_JA_edit_mode:
            self.save_title_dro()
        if self.conv_face_spiral_rect == 'spiral':
            self.set_image('face_spiral_rect_btn_image', 'face_spiral_rect_rect_highlight.png')
            self.set_image('conv_face_main_image', 'mill_conv_face_rect_main.svg')
        else:
            self.set_image('face_spiral_rect_btn_image', 'face_spiral_rect_spiral_highlight.png')
            self.set_image('conv_face_main_image', 'mill_conv_face_main.svg')

        self.face_dro_list['face_x_start_dro'].grab_focus()
        self.conv_face_spiral_rect = 'spiral' if self.conv_face_spiral_rect == 'rect' else 'rect'
        if not self.in_JA_edit_mode:
            self.load_title_dro()

    def on_face_spiral_rect_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.on_face_spiral_rect_set_state()


    def on_face_x_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.face_dro_list['face_x_end_dro'].grab_focus()
        return

    def on_face_x_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.face_dro_list['face_y_start_dro'].grab_focus()
        return

    def on_face_y_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.face_dro_list['face_y_end_dro'].grab_focus()
        return

    def on_face_y_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.face_dro_list['face_z_start_dro'].grab_focus()
        return

    def on_face_z_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.face_dro_list['face_z_end_dro'].grab_focus()
        return

    def on_face_z_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.face_dro_list['face_z_doc_dro'].grab_focus()
        return


    def on_face_z_doc_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.face_dro_list['face_stepover_dro'].grab_focus()
        return

    def on_face_stepover_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        tool_number = int(self.conv_dro_list['conv_tool_number_dro'].get_text())
        tool_dia = self.status.tool_table[tool_number].diameter * self.ttable_conv
        stepover_hint = .7 * tool_dia
        self.face_stepover_hint_label.set_markup('<span weight="light" font_desc="Bebas 8" font_stretch="ultracondensed" foreground="white">(.7    *    %s    tool    dia.    =    %s)</span>' % (self.dro_long_format, self.dro_long_format) % (tool_dia, stepover_hint))

        widget.set_text(self.dro_long_format % value)
        self.face_dro_list['face_x_start_dro'].grab_focus()
        return

    # -------------------------------------------------------------------------------------------------
    # Conversational
    # Profile DRO handlers
    # -------------------------------------------------------------------------------------------------
    def on_profile_rect_circ_set_state(self):
        self.save_title_dro()
        if self.conv_profile_rect_circ == 'rect':
            self.set_image('profile_rect_circ_btn_image', 'pocket_rect_circ_circ_highlight.jpg')
            self.set_image('conv_profile_main_image', 'mill_conv_profile_circ.1.svg')
            rect_state = False
            circ_state = True
            self.conv_profile_rect_circ = 'circ'
            if not len(self.profile_dro_list['profile_circ_z_doc_dro'].get_text()):
                self.profile_dro_list['profile_circ_z_doc_dro'].set_text(self.profile_dro_list['profile_z_doc_dro'].get_text())
            if not len(self.profile_dro_list['profile_circ_z_end_dro'].get_text()):
                self.profile_dro_list['profile_circ_z_end_dro'].set_text(self.profile_dro_list['profile_z_end_dro'].get_text())
            if not len(self.profile_dro_list['profile_circ_z_start_dro'].get_text()):
                self.profile_dro_list['profile_circ_z_start_dro'].set_text(self.profile_dro_list['profile_z_start_dro'].get_text())
            if not len(self.profile_dro_list['profile_circ_stepover_dro'].get_text()):
                self.profile_dro_list['profile_circ_stepover_dro'].set_text(self.profile_dro_list['profile_stepover_dro'].get_text())
            if not len(self.profile_dro_list['profile_circ_x_start_dro'].get_text()):
                self.profile_dro_list['profile_circ_x_start_dro'].set_text(self.profile_dro_list['profile_x_start_dro'].get_text())
            if not len(self.profile_dro_list['profile_circ_x_end_dro'].get_text()):
                self.profile_dro_list['profile_circ_x_end_dro'].set_text(self.profile_dro_list['profile_x_end_dro'].get_text())
            if not len(self.profile_dro_list['profile_circ_y_start_dro'].get_text()):
                self.profile_dro_list['profile_circ_y_start_dro'].set_text(self.profile_dro_list['profile_y_start_dro'].get_text())
            if not len(self.profile_dro_list['profile_circ_y_end_dro'].get_text()):
                self.profile_dro_list['profile_circ_y_end_dro'].set_text(self.profile_dro_list['profile_y_end_dro'].get_text())
            self.profile_dro_list['profile_circ_x_start_dro'].grab_focus()
        else:
            self.set_image('profile_rect_circ_btn_image', 'pocket_rect_circ_rect_highlight.jpg')
            self.set_image('conv_profile_main_image', 'mill_conv_profile_main.svg')
            rect_state = True
            circ_state = False
            self.conv_profile_rect_circ = 'rect'
            self.profile_dro_list['profile_x_prfl_start_dro'].grab_focus()

        # set rect DROs
        self.profile_dro_list['profile_z_doc_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_z_end_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_z_start_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_stepover_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_x_start_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_x_end_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_y_start_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_y_end_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_x_prfl_start_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_x_prfl_end_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_y_prfl_start_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_y_prfl_end_dro'].set_visible(rect_state)
        self.profile_dro_list['profile_radius_dro'].set_visible(rect_state)
        # set circ DROs
        self.profile_dro_list['profile_circ_z_doc_dro'].set_visible(circ_state)
        self.profile_dro_list['profile_circ_z_end_dro'].set_visible(circ_state)
        self.profile_dro_list['profile_circ_z_start_dro'].set_visible(circ_state)
        self.profile_dro_list['profile_circ_stepover_dro'].set_visible(circ_state)
        self.profile_dro_list['profile_circ_x_start_dro'].set_visible(circ_state)
        self.profile_dro_list['profile_circ_x_end_dro'].set_visible(circ_state)
        self.profile_dro_list['profile_circ_y_start_dro'].set_visible(circ_state)
        self.profile_dro_list['profile_circ_y_end_dro'].set_visible(circ_state)
        self.profile_dro_list['profile_circ_diameter_dro'].set_visible(circ_state)
        self.profile_dro_list['profile_x_center_dro'].set_visible(circ_state)
        self.profile_dro_list['profile_y_center_dro'].set_visible(circ_state)

        # turn rect labels(text) OFF
        self.profile_x_prfl_start_label.set_visible(rect_state)
        self.profile_x_prfl_end_label.set_visible(rect_state)
        self.profile_y_prfl_start_label.set_visible(rect_state)
        self.profile_y_prfl_end_label.set_visible(rect_state)
        self.profile_radius_label.set_visible(rect_state)

        # turn circ labels(text) ON
        self.profile_circ_diameter_label.set_visible(circ_state)
        self.profile_x_center_label.set_visible(circ_state)
        self.profile_y_center_label.set_visible(circ_state)
        self.load_title_dro()


    def on_profile_rect_circ_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # toggle button state between rect and circ
        self.on_profile_rect_circ_set_state()

    def on_profile_radius_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_y_start_dro'].grab_focus()
        return

    def on_profile_z_doc_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_z_start_dro'].grab_focus()
        return

    def on_profile_x_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_x_end_dro'].grab_focus()
        return

    def on_profile_x_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_x_prfl_start_dro'].grab_focus()
        return

    def on_profile_y_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_y_prfl_start_dro'].grab_focus()
        return

    def on_profile_y_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        goto_dro = 'profile_stepover_dro' if self.conv_profile_rect_circ == 'rect' else 'profile_circ_diameter_dro'
        self.profile_dro_list[goto_dro].grab_focus()
        return

    def on_profile_stepover_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        tool_number = int(self.conv_dro_list['conv_tool_number_dro'].get_text())
        tool_dia = self.status.tool_table[tool_number].diameter * self.ttable_conv
        stepover_hint = .7 * tool_dia
        self.profile_stepover_hint_label.set_markup('<span weight="light" font_desc="Bebas 8" font_stretch="ultracondensed" foreground="white">(.7    *    %s    tool    dia.    =    %s)</span>' % (self.dro_long_format, self.dro_long_format) % (tool_dia, stepover_hint))

        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_z_doc_dro'].grab_focus()
        return

    def on_profile_z_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_z_end_dro'].grab_focus()
        return

    def on_profile_z_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_x_start_dro'].grab_focus()
        return

    def on_profile_x_prfl_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_x_prfl_end_dro'].grab_focus()
        return

    def on_profile_x_prfl_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_radius_dro'].grab_focus()
        return

    def on_profile_y_prfl_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_y_prfl_end_dro'].grab_focus()
        return

    def on_profile_y_prfl_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_y_end_dro'].grab_focus()
        return

    # .. circ ...........
    def on_profile_circ_stepover_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_circ_z_doc_dro'].grab_focus()
        return

    def on_profile_circ_z_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_circ_z_end_dro'].grab_focus()
        return

    def on_profile_circ_z_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_circ_x_start_dro'].grab_focus()
        return

    def on_profile_circ_z_doc_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_circ_z_start_dro'].grab_focus()
        return

    def on_profile_circ_x_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_circ_x_end_dro'].grab_focus()
        return

    def on_profile_circ_x_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_circ_y_start_dro'].grab_focus()
        return

    def on_profile_circ_y_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_circ_y_end_dro'].grab_focus()
        return

    def on_profile_circ_y_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_circ_diameter_dro'].grab_focus()
        return
    def on_profile_circ_diameter_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_x_center_dro'].grab_focus()
        return

    def on_profile_x_center_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_y_center_dro'].grab_focus()
        return

    def on_profile_y_center_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.profile_dro_list['profile_circ_stepover_dro'].grab_focus()
        return



    # -------------------------------------------------------------------------------------------------
    # Conversational
    # Pocket DRO handlers
    # -------------------------------------------------------------------------------------------------
    def on_pocket_rect_circ_set_state(self):
        self.save_title_dro()
        if self.conv_pocket_rect_circ == 'rect':
            self.set_image('pocket_rect_circ_btn_image', 'pocket_rect_circ_circ_highlight.jpg')
            self.set_image('conv_pocket_main_image', 'mill_conv_pocket_circ_main.svg')
            rect_state = False
            circ_state = True
            self.conv_pocket_rect_circ = 'circ'
        else:
            self.set_image('pocket_rect_circ_btn_image', 'pocket_rect_circ_rect_highlight.jpg')
            self.set_image('conv_pocket_main_image', 'mill_conv_pocket_rect_main.svg')
            rect_state = True
            circ_state = False
            self.conv_pocket_rect_circ = 'rect'

        # set rect DROs
        self.pocket_rect_dro_list['pocket_rect_x_start_dro'].set_visible(rect_state)
        self.pocket_rect_dro_list['pocket_rect_x_end_dro'].set_visible(rect_state)
        self.pocket_rect_dro_list['pocket_rect_y_start_dro'].set_visible(rect_state)
        self.pocket_rect_dro_list['pocket_rect_y_end_dro'].set_visible(rect_state)
        self.pocket_rect_dro_list['pocket_rect_z_start_dro'].set_visible(rect_state)
        self.pocket_rect_dro_list['pocket_rect_z_end_dro'].set_visible(rect_state)
        self.pocket_rect_dro_list['pocket_rect_z_doc_dro'].set_visible(rect_state)
        self.pocket_rect_dro_list['pocket_rect_stepover_dro'].set_visible(rect_state)
        self.pocket_rect_dro_list['pocket_rect_corner_radius_dro'].set_visible(rect_state)

        # set circ DROs
        self.pocket_circ_dro_list['pocket_circ_z_end_dro'].set_visible(circ_state)
        self.pocket_circ_dro_list['pocket_circ_z_start_dro'].set_visible(circ_state)
        self.pocket_circ_dro_list['pocket_circ_z_doc_dro'].set_visible(circ_state)
        self.pocket_circ_dro_list['pocket_circ_stepover_dro'].set_visible(circ_state)
        self.pocket_circ_dro_list['pocket_circ_diameter_dro'].set_visible(circ_state)

        # turn rect labels(text) OFF
        self.pocket_rect_x_start_label.set_visible(rect_state)
        self.pocket_rect_x_end_label.set_visible(rect_state)
        self.pocket_rect_y_start_label.set_visible(rect_state)
        self.pocket_rect_y_end_label.set_visible(rect_state)
        self.pocket_rect_corner_radius_label.set_visible(rect_state)

        # turn circ labels(text) ON
        self.pocket_circ_x_center_label.set_visible(circ_state)
        self.pocket_circ_y_center_label.set_visible(circ_state)
        self.pocket_circ_diameter_label.set_visible(circ_state)

        if self.conv_pocket_rect_circ == 'rect':
            self.pocket_rect_dro_list['pocket_rect_x_start_dro'].grab_focus()
        else:
            self.pocket_circ_dro_list['pocket_circ_diameter_dro'].grab_focus()
        self.load_title_dro()

        ## Some conv_DROs may also be set with on_conv_notebook_switch_page

    def on_pocket_rect_circ_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.on_pocket_rect_circ_set_state()

    # *****  Rectangular DRO handlers  *****
    def on_pocket_rect_x_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_rect_dro_list['pocket_rect_x_end_dro'].grab_focus()
        return

    def on_pocket_rect_x_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_rect_dro_list['pocket_rect_corner_radius_dro'].grab_focus()
        return

    def on_pocket_rect_corner_radius_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_rect_dro_list['pocket_rect_y_start_dro'].grab_focus()
        return

    def on_pocket_rect_y_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_rect_dro_list['pocket_rect_y_end_dro'].grab_focus()
        return

    def on_pocket_rect_y_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_rect_dro_list['pocket_rect_z_start_dro'].grab_focus()
        return

    def on_pocket_rect_z_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_rect_dro_list['pocket_rect_z_end_dro'].grab_focus()
        return

    def on_pocket_rect_z_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_rect_dro_list['pocket_rect_z_doc_dro'].grab_focus()
        return

    def on_pocket_rect_z_doc_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_rect_dro_list['pocket_rect_stepover_dro'].grab_focus()
        return

    def on_pocket_rect_stepover_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        tool_number = int(self.conv_dro_list['conv_tool_number_dro'].get_text())
        tool_dia = self.status.tool_table[tool_number].diameter * self.ttable_conv
        stepover_hint = .7 * tool_dia
        self.pocket_rect_stepover_hint_label.set_markup('<span weight="light" font_desc="Bebas 8" font_stretch="ultracondensed" foreground="white">(.7    *    %s    tool    dia.    =\n    %s)</span>' % (self.dro_long_format, self.dro_long_format) % (tool_dia, stepover_hint))

        widget.set_text(self.dro_long_format % value)
        self.pocket_rect_dro_list['pocket_rect_x_start_dro'].grab_focus()
        return


    # -------------------------------------------------------------------------------------------------
    # Conversational
    # Pocket-Circular DRO handlers
    # -------------------------------------------------------------------------------------------------

    def on_pocket_circ_diameter_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_circ_dro_list['pocket_circ_z_start_dro'].grab_focus()
        return

    def on_pocket_circ_z_start_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_circ_dro_list['pocket_circ_z_end_dro'].grab_focus()
        return

    def on_pocket_circ_z_end_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_circ_dro_list['pocket_circ_z_doc_dro'].grab_focus()
        return

    def on_pocket_circ_z_doc_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        self.pocket_circ_dro_list['pocket_circ_stepover_dro'].grab_focus()
        return

    def on_pocket_circ_stepover_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        tool_number = int(self.conv_dro_list['conv_tool_number_dro'].get_text())
        tool_dia = self.status.tool_table[tool_number].diameter * self.ttable_conv
        stepover_hint = .7 * tool_dia
        #self.pocket_circ_stepover_hint_label.set_markup('<span weight="light" font_desc="Bebas 8" font_stretch="ultracondensed" foreground="white">(.7    *    %s    tool    dia.    =    %s)</span>' % (self.dro_long_format, self.dro_long_format) % (tool_dia, stepover_hint))
        self.pocket_rect_stepover_hint_label.set_markup('<span weight="light" font_desc="Bebas 8" font_stretch="ultracondensed" foreground="white">(.7    *    %s    tool    dia.    =\n    %s)</span>' % (self.dro_long_format, self.dro_long_format) % (tool_dia, stepover_hint))

        widget.set_text(self.dro_long_format % value)
        self.pocket_circ_dro_list['pocket_circ_diameter_dro'].grab_focus()
        return


    # -------------------------------------------------------------------------------------------------
    # Conversational
    # Drill-Tap DRO handlers
    # -------------------------------------------------------------------------------------------------

    def calc_tap_z_feed_rate(self):
        z_tap_feed_str = self.current_normal_z_feed_rate
        try:  # calculate related Z feed DRO
            pitch = float(self.tap_dro_list['tap_pitch_dro'].get_text())
            rpm = float(self.conv_dro_list['conv_rpm_dro'].get_text())
            z_feed = pitch * rpm
            z_tap_feed_str = self.dro_medium_format % z_feed
        except:
            z_tap_feed_str = self.current_normal_z_feed_rate
        return z_tap_feed_str


    def update_drill_through_hole_hint(self):
        self._update_drill_through_hole_hint_label(self.conv_dro_list['conv_tool_number_dro'].get_text(),
                                                   self.drill_dro_list['drill_z_end_dro'].get_text(),
                                                   self.drill_through_hole_hint_label)

    def update_drill_z_feed_per_rev_hint(self):
        try: # try here becuase these may be empty...
            rpm = float(self.conv_dro_list['conv_rpm_dro'].get_text())
            z_feed = float(self.conv_dro_list['conv_z_feed_dro'].get_text())
            z_feed_per_rev = z_feed / rpm
            markup_str = '<span weight="light" font_desc="Bebas 8" font_stretch="ultracondensed" foreground="white">(Z    feed    per    revolution    :    %s)</span>'
            self.drill_z_feed_per_rev_hint.set_markup(markup_str % (self.dro_long_format) % (z_feed_per_rev))
        except:
            pass

    def show_hide_dros(self, show=True):
        for dro in self.drill_dro_list.values():
            dro.set_visible(show)
        for label in self.drill_labels.values():
            label.set_visible(show)
        for item in self.drill_tap_extras.values():
            item.set_visible(show)

    def on_conv_drill_tap_pattern_notebook_switch_page(self, notebook, page, page_num):
        if page_num == 0: #pattern
            self.drill_pattern_notebook_page = 'pattern'
        elif page_num == 1: #circular
            self.drill_pattern_notebook_page = 'circular'
        return

        # toggle button state between drill and tap
    def on_drill_tap_set_state(self):
        z_tap_feed_str = self.calc_tap_z_feed_rate()
        self.save_title_dro()
        if self.conv_drill_tap == 'drill':
            self.set_image('drill_tap_btn_image', 'drill_tap_tap_highlight.jpg')
            self.set_image('drill_tap_main_image', 'mill_drill_tap_main.png')
            self.set_image('drill_tap_detail_image', 'mill_tap_detail.png')
            self.conv_dro_list['conv_z_feed_dro'].set_sensitive(False)
            self.checkbutton_list['tap_2x_checkbutton'].set_visible(True)
            self.tap_hsep.set_visible(True)
            self.drill_through_hole_hint_label.set_visible(False)
            self.drill_z_feed_per_rev_hint.set_visible(False)
            show_drill = False
            show_tap = True
            self.conv_dro_list['conv_z_feed_dro'].set_text(z_tap_feed_str)
            self.conv_drill_tap = 'tap'

        else:
            self.set_image('drill_tap_btn_image', 'drill_tap_drill_highlight.jpg')
            self.set_image('drill_tap_main_image', 'mill_drill_main.png')
            self.set_image('drill_tap_detail_image', 'mill_drill_peck_detail.png')
            self.conv_dro_list['conv_z_feed_dro'].set_sensitive(True)
            self.checkbutton_list['tap_2x_checkbutton'].set_visible(False)
            self.tap_hsep.set_visible(False)
            self.drill_through_hole_hint_label.set_visible(True)
            self.drill_z_feed_per_rev_hint.set_visible(True)
            show_drill = True
            show_tap = False
            if z_tap_feed_str != self.current_normal_z_feed_rate:
                self.conv_dro_list['conv_z_feed_dro'].set_text(self.current_normal_z_feed_rate)
            self.conv_drill_tap = 'drill'

        # Update visibility of drill labels / DRO's
        for label in self.drill_dro_list.values():
            label.set_visible(show_drill)
        for label in self.drill_labels.values():
            label.set_visible(show_drill)
        # Update visibility of tap labels / DRO's
        for label in self.tap_labels.values():
            label.set_visible(show_tap)
        for label in self.tap_dro_list.values():
            label.set_visible(show_tap)
        if self.conv_drill_tap == 'drill':
            self.drill_dro_list['drill_peck_dro'].grab_focus()
        else:
            self.tap_dro_list['tap_pitch_dro'].grab_focus()
        self.load_title_dro()


    def on_drill_tap_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        # toggle button state between drill and tap
        self.on_drill_tap_set_state()

    def on_drill_z_start_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.drill_dro_list['drill_z_end_dro'].grab_focus()
        return

    def on_drill_peck_dro_activate(self, widget, data=None):
        (valid, peck, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        try:
            dwell = float(self.drill_dro_list['drill_dwell_dro'].get_text())
            if dwell > 0 and peck > 0:
                dwell = 0.0
                self.drill_dro_list['drill_dwell_dro'].set_text('%s' % self.dro_dwell_format % dwell)
                try:  # if RPM and Dwell are okay, do calc
                    rpm = float(self.conv_dro_list['conv_rpm_dro'].get_text())
                    #dwell_revs = rpm * min/sec * dwell
                    dwell_revs = rpm * dwell / 60
                    self.drill_labels['dwell_revs_calc'].modify_font(self.drill_calc_font)
                    self.drill_labels['dwell_revs_calc'].set_markup('<span foreground="white">%s</span>' % self.dro_medium_format % dwell_revs)
                except:  # clear any value in Dwell Revs label
                    self.drill_labels['dwell_revs_calc'].set_text('')

        except:
            pass

        widget.set_text('%s' % self.dro_long_format % peck)
        self.drill_dro_list['drill_z_start_dro'].grab_focus()
        return

    def on_drill_z_end_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.update_drill_through_hole_hint()
        if self.drill_pattern_notebook_page == 'pattern':
            self.drill_dro_list['drill_spot_tool_number_dro'].grab_focus()
        else:
            self.drill_circular_dro_list['drill_tap_pattern_circular_holes_dro'].grab_focus()
        return

    def on_drill_dwell_dro_activate(self, widget, data=None):
        (valid, dwell, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        try:
            peck = float(self.drill_dro_list['drill_peck_dro'].get_text())
            if dwell > 0 and peck > 0:
                peck = 0.0
                self.drill_dro_list['drill_peck_dro'].set_text('%s' % self.dro_long_format % peck)
        except:
            pass

        widget.set_text('%s' % self.dro_dwell_format % dwell)

        try:  # if RPM and Dwell are okay, do calc
            rpm = float(self.conv_dro_list['conv_rpm_dro'].get_text())
            #dwell_revs = rpm * min/sec * dwell
            dwell_revs = rpm * dwell / 60
            self.drill_labels['dwell_revs_calc'].modify_font(self.drill_calc_font)
            self.drill_labels['dwell_revs_calc'].set_markup('<span foreground="white">%s</span>' % self.dro_medium_format % dwell_revs)
        except:  # clear any value in Dwell Revs label
            self.drill_labels['dwell_revs_calc'].set_text('')

        self.drill_dro_list['drill_peck_dro'].grab_focus()
        return

    def on_drill_spot_tool_number_dro_activate(self, widget, data=None):
        # empty dro is valid here...
        text = widget.get_text()
        if len(text) > 0:
            (valid, number, error_msg) = self.conversational.validate_param(widget)
            if not valid:
                self.error_handler.write('Conversational Drilling entry error - ' + error_msg, ALARM_LEVEL_LOW)
                return
            text = str(number) if number is not None else ''
            widget.set_text(text)
        else:
            mill_conversational.raise_alarm(self.drill_dro_list['drill_spot_tool_doc_dro'],False)
        self.drill_dro_list['drill_spot_tool_doc_dro'].grab_focus()
        return

    def on_drill_spot_tool_doc_dro_activate(self, widget, data=None):
        spot_dro = self.drill_dro_list['drill_spot_tool_number_dro']
        text = widget.get_text()
        spot_text = spot_dro.get_text()
        if len(spot_text) == 0 and len(text) == 0:
            mill_conversational.raise_alarm(widget,False)
            self.drill_dro_list['drill_peck_dro'].grab_focus()
            return
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        if number is None:
            widget.set_text('')
        else:
            widget.set_text('%s' % self.dro_long_format % number)
        self.drill_dro_list['drill_peck_dro'].grab_focus()
        return

    def on_drill_tap_pattern_circular_holes_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        text = str(number) if number is not None else ''
        widget.set_text(text)
        self.on_complete_circle_data()
        self.drill_circular_dro_list['drill_tap_pattern_circular_start_angle_dro'].grab_focus()
        return

    def on_drill_tap_pattern_circular_start_angle_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.on_complete_circle_data()
        self.drill_circular_dro_list['drill_tap_pattern_circular_diameter_dro'].grab_focus()
        return

    def on_drill_tap_pattern_circular_diameter_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.on_complete_circle_data()
        self.drill_circular_dro_list['drill_tap_pattern_circular_center_x_dro'].grab_focus()
        return

    def on_drill_tap_pattern_circular_center_x_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.on_complete_circle_data()
        self.drill_circular_dro_list['drill_tap_pattern_circular_center_y_dro'].grab_focus()
        return

    def on_drill_tap_pattern_circular_center_y_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.on_complete_circle_data()
#       self.drill_circular_dro_list['drill_tap_pattern_circular_holes_dro'].grab_focus()
        self.drill_dro_list['drill_spot_tool_number_dro'].grab_focus()
        return

    def on_complete_circle_data(self):
        (valid, holes) = mill_conversational.is_number_or_expression(self.drill_circular_dro_list['drill_tap_pattern_circular_holes_dro'])
        if valid == False or holes <= 0:
            return

        (valid, angle) = mill_conversational.is_number_or_expression(self.drill_circular_dro_list['drill_tap_pattern_circular_start_angle_dro'])
        if valid == False or -90 > angle > 90:
            return

        (valid, diameter) = mill_conversational.is_number_or_expression(self.drill_circular_dro_list['drill_tap_pattern_circular_diameter_dro'])
        if valid == False or diameter <= 0:
            return

        (valid, center_x) = mill_conversational.is_number_or_expression(self.drill_circular_dro_list['drill_tap_pattern_circular_center_x_dro'])
        if valid == False:
            return

        (valid, center_y) = mill_conversational.is_number_or_expression(self.drill_circular_dro_list['drill_tap_pattern_circular_center_y_dro'])
        if valid == False:
            return

        old_drill_limit = self.DRILL_TABLE_ROWS
        self.DRILL_TABLE_ROWS = DRILL_TABLE_BASIC_SIZE if int(holes) <= DRILL_TABLE_BASIC_SIZE else int(holes)

        # generate the 'new drill liststore'
        radius = float(diameter / float(2))
        hole_degrees = float(360 / float(holes))
        hole_number = 1
        for row in range(self.DRILL_TABLE_ROWS):
            if hole_number <= int(holes):
                x_value = center_x + (radius * math.cos(math.radians(angle)))
                y_value = center_y + (radius * math.sin(math.radians(angle)))
                if row < old_drill_limit:
                    self.drill_liststore[row][1] = '%.4f' % x_value
                    self.drill_liststore[row][2] = '%.4f' % y_value
                else:
                    self.drill_liststore.append([hole_number, '%.4f' % x_value, '%.4f' % y_value])
                angle += hole_degrees
            else:
                self.drill_liststore[row][0] = (hole_number)
                self.drill_liststore[row][1] = ''
                self.drill_liststore[row][2] = ''
            hole_number += 1

        # reduce the size of liststore back to the basic size if larger size no longer needed
        if old_drill_limit > self.DRILL_TABLE_ROWS:
            new_upper_limit = DRILL_TABLE_BASIC_SIZE if int(holes) <= DRILL_TABLE_BASIC_SIZE else int(holes)
            print 'old_limit: %d new_limit: %d' % (old_drill_limit,new_upper_limit)
            for row in range(new_upper_limit, old_drill_limit):
                iter_index = self.drill_liststore.iter_n_children(None)
                iter = self.drill_liststore.iter_nth_child(None, iter_index - 1)
                self.drill_liststore.remove(iter)

        return

    # *****  Drill Table Handlers  *****
    def drill_liststore_to_list(self):
        out_list = []
        for row in self.drill_liststore:
            out_list.append((row[0],row[1],row[2]))
        return out_list

    def list_to_drill_liststore(self, in_list):
        if in_list is None:
            return
        self.drill_liststore.clear()
        for item in in_list:
            self.drill_liststore.append([item[0],item[1],item[2]])

    def drill_table_update_focus(self,row,column,start_editing):
        print 'drill_table_update_focus - row: %d, column: %s, start editing %s' % (row,column.get_title(),'%s') % 'True' if start_editing else 'False'
        self.drill_treeview.set_cursor(row, column, start_editing)
        if start_editing:
            self.dt_scroll_adjust(row)

    def on_drill_x_column_keypress(self,widget,ev,row):
        print 'in on_drill_x_column_keypress'
        print 'keypress = %s' % gtk.gdk.keyval_name(ev.keyval)
        if ev.keyval == gtk.keysyms.Return:
            glib.idle_add(self.drill_table_update_focus,row, self.drill_y_column,True)
            return False
        if ev.keyval == gtk.keysyms.Escape:
            print "escape hit"
            glib.idle_add(self.drill_table_update_focus,row, self.drill_x_column,False)
            return True

    def on_drill_y_column_keypress(self,widget,ev,row):
        print 'in on_drill_y_column_keypress'
        print 'keypress = %s' % gtk.gdk.keyval_name(ev.keyval)
        if ev.keyval == gtk.keysyms.Return:
            glib.idle_add(self.drill_table_update_focus,row, self.drill_x_column,True)
            return False
        if ev.keyval == gtk.keysyms.Escape:
            print "escape hit"
            target_row = 0 if row == 0 else row - 1
            glib.idle_add(self.drill_table_update_focus,target_row, self.drill_y_column,False)
            return True

    def on_drill_x_column_activate(self,widget,row):
        print 'in on_drill_x_column_activate'
        if ev.keyval == gtk.keysyms.Return:
            glib.idle_add(self.drill_table_update_focus,row, self.drill_y_column,True)
        return False

    def on_drill_y_column_activate(self,widget,row):
        print 'in on_drill_y_column_activate'
        if ev.keyval == gtk.keysyms.Return:
            glib.idle_add(self.drill_table_update_focus,row, self.drill_x_column,True)
        return False

    def on_drill_cell_edit_x_focus(self, widget, direction, target_row):
        print 'in on_drill_cell_edit_x_focus'
        if self.touchscreen_enabled:
            numpad.numpad_popup(widget,False,-324,-119)
            widget.masked = 0
            widget.select_region(0, 0)
            self.window.set_focus(None)
            widget.connect("activate", self.on_drill_x_column_activate, target_row)

    def on_drill_cell_edit_y_focus(self, widget, direction, target_row):
        print 'in on_drill_cell_edit_y_focus'
        if self.touchscreen_enabled:
            numpad.numpad_popup(widget,False,-324,-119)
            widget.masked = 0
            widget.select_region(0, 0)
            self.window.set_focus(None)
            widget.connect("activate", self.on_drill_y_column_activate, target_row)

    def on_drill_x_column_editing_started(self, xrenderer, editable, path, drill_font):
        print "Editing *started* X column : on_drill_x_column_editing_started"
        editable.modify_font(drill_font)
        target_row = 0 if path == '' else int(path)
        if self.touchscreen_enabled:
            editable.connect("focus-in-event", self.on_drill_cell_edit_x_focus, target_row)
        editable.connect("key-press-event", self.on_drill_x_column_keypress, target_row)

    def on_drill_y_column_editing_started(self, yrenderer, editable, path, drill_font):
        print "Editing *started* Y column : on_drill_y_column_editing_started"
        editable.modify_font(drill_font)
        row = 0 if path == '' else int(path)
        target_row = None
        if row >= (self.DRILL_TABLE_ROWS - 1):
            target_row = (self.DRILL_TABLE_ROWS - 1)
        else:
            target_row = row + 1
        if self.touchscreen_enabled:
            editable.connect("focus-in-event", self.on_drill_cell_edit_y_focus, target_row)
        editable.connect("key-press-event", self.on_drill_y_column_keypress, target_row)

    def on_drill_x_column_edited(self, cell, row, value, model):
        if value == '' or value == '??':
            model[row][1] = ""
            return

        valid, value, error_msg = self.conversational.validate_drill_pos(value, 'X')
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        row = 0 if row == '' else int(row)
        model[row][1] = "%0.4f" % value

    def on_drill_y_column_edited(self, cell, row, value, model):
        if value == '' or value == '??':
            model[row][2] = ""
            return

        valid, value, error_msg = self.conversational.validate_drill_pos(value, 'Y')
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        row = 0 if row == '' else int(row)
        model[row][2] = "%0.4f" % value

    def on_drill_tap_clear_table_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return

        self.drill_liststore.clear()

        for id_cnt  in range(1, self.DRILL_TABLE_ROWS + 1):
            self.drill_liststore.append([id_cnt, '', ''])

        adj = self.scrolled_window_drill_table.get_vadjustment()
        adj.set_value(0)

        self.drill_treeview.set_cursor(0, focus_column=self.drill_x_column, start_editing=True)

        return

    def on_drill_tap_raise_in_table_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return

        selection = self.drill_treeview.get_selection()
        model, selected_iter = selection.get_selected()
        if selected_iter: #result could be None
            selected_row = model.get_path(selected_iter)[0]
            if selected_row > 0:
                target_iter = model.get_iter(selected_row - 1)
                model.move_before(selected_iter, target_iter)

                for i in range(self.DRILL_TABLE_ROWS):  # reset ID column numbers
                    model[i][0] = i + 1
            self.dt_scroll_adjust(selected_row - 1)
        return

    def on_drill_tap_lower_in_table_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return

        selection = self.drill_treeview.get_selection()
        model, selected_iter = selection.get_selected()
        if selected_iter: #result could be None
            selected_row = model.get_path(selected_iter)[0]
            if selected_row < (self.DRILL_TABLE_ROWS - 1):
                target_iter = model.get_iter(selected_row + 1)
                model.move_after(selected_iter, target_iter)

                for i in range(self.DRILL_TABLE_ROWS):  # reset ID column numbers
                    model[i][0] = i + 1
            self.dt_scroll_adjust(selected_row + 1)
        return

    def on_drill_tap_insert_row_table_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return

        selection = self.drill_treeview.get_selection()
        model, selected_iter = selection.get_selected()
        if selected_iter: #result could be None
            selected_row = model.get_path(selected_iter)[0]
            new_iter = model.insert_before(selected_iter,['','',''])
            last_iter = None
            while selected_iter:
                last_iter = selected_iter
                selected_iter = model.iter_next(selected_iter)
            if last_iter:
                model.remove(last_iter)

            for i in range(self.DRILL_TABLE_ROWS):  # reset ID column numbers
                model[i][0] = i + 1
            self.dt_scroll_adjust(selected_row)
            selection.select_iter(new_iter)
        return

    def on_drill_tap_delete_row_table_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return

        selection = self.drill_treeview.get_selection()
        model, selected_iter = selection.get_selected()
        if selected_iter: #result could be None
            selected_row = model.get_path(selected_iter)[0]
            model.remove( selected_iter )
            # add an empty row at the end
            model.append(['', '', ''])

            for i in range(self.DRILL_TABLE_ROWS):  # reset ID column numbers
                model[i][0] = i + 1
            self.dt_scroll_adjust(selected_row)
        return

    def dt_scroll_adjust(self, row):
        # get var list from vertical scroll bar
        adj = self.scrolled_window_drill_table.get_vadjustment()

        unitsperrow = (adj.upper - adj.lower) / self.DRILL_TABLE_ROWS
        centerofpage = adj.page_size / 2
        centerofrow = unitsperrow / 2
        cofcurrentrow = (row * unitsperrow) + centerofrow
        scroll_offset = cofcurrentrow - centerofpage

        if scroll_offset < 0:
            scroll_offset = 0
        elif scroll_offset > (adj.upper - adj.page_size):
            scroll_offset = (adj.upper - adj.page_size)

        adj.set_value(scroll_offset)


    # *****  Tap DRO Handlers  *****
    def on_tap_z_start_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.tap_dro_list['tap_z_end_dro'].grab_focus()
        return

    def on_tap_z_end_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.tap_dro_list['tap_dwell_dro'].grab_focus()
        return

    def on_tap_dwell_dro_map(self, widget, data=None):
        text = widget.get_text()
        if text == '':
            widget.set_text('0.00')
        try:
            if float(text) == 0:
                self.tap_labels['dwell_travel_calc'].modify_font(self.drill_calc_font)
                self.tap_labels['dwell_travel_calc'].set_markup('<span foreground="white">0.00</span>')
        except:
            pass
        return

    def on_tap_dwell_dro_activate(self, widget, data=None):
        (valid, dwell, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_dwell_format % dwell)

        try:  # if RPM and Dwell are okay, do calc
            rpm = float(self.conv_dro_list['conv_rpm_dro'].get_text())
            pitch = float(self.tap_dro_list['tap_pitch_dro'].get_text())
            # half_dwell_travel = dwell * rpm * min/60s * pitch * 1/2
            half_dwell_travel = (dwell * rpm * pitch) / 120
            self.tap_labels['dwell_travel_calc'].modify_font(self.drill_calc_font)
            self.tap_labels['dwell_travel_calc'].set_markup('<span foreground="white">%s</span>' % self.dro_dwell_format % half_dwell_travel)
        except:  # clear any value in Dwell Revs label
            self.tap_labels['dwell_travel_calc'].set_text('')

        self.tap_dro_list['tap_pitch_dro'].grab_focus()
        return

    def on_tap_pitch_dro_activate(self, widget, data=None):
        (valid, pitch, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % pitch)

        tpu = 1 / pitch
        self.tap_dro_list["tap_tpu_dro"].set_text(self.dro_medium_format % tpu)

        try:
            rpm = float(self.conv_dro_list['conv_rpm_dro'].get_text())
            feed = pitch * rpm
            self.conv_dro_list['conv_z_feed_dro'].set_text(self.dro_medium_format % feed)

        except:
            self.conv_dro_list['conv_z_feed_dro'].set_text('')

        self.tap_dro_list['tap_tpu_dro'].grab_focus()
        return

    def on_tap_tpu_dro_activate(self, widget, data=None):
        (valid, tpu, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_medium_format % tpu)

        pitch = 1 / tpu
        self.tap_dro_list["tap_pitch_dro"].set_text(self.dro_long_format % pitch)

        try:
            rpm = float(self.conv_dro_list['conv_rpm_dro'].get_text())
            feed = pitch * rpm
            self.conv_dro_list['conv_z_feed_dro'].set_text(self.dro_medium_format % feed)

        except:
            self.conv_dro_list['conv_z_feed_dro'].set_text('')

        self.tap_dro_list['tap_z_end_dro'].grab_focus()
        return

    def on_tap_2x_checkbutton_toggled(self, widget, data=None):
        self.tap_2x_enabled = widget.get_active()

    # -------------------------------------------------------------------------------------------------
    # Conversational
    # Thread Mill DRO handlers
    # -------------------------------------------------------------------------------------------------

    def on_thread_mill_ext_int_set_state(self):
        self.save_title_dro()
        if self.conv_thread_mill_ext_int == 'external':
            self.set_image('thread_mill_ext_int_btn_image', 'thread_int_button.jpg')
            self.image_list['thread_mill_main_image'].set_from_file(os.path.join(GLADE_DIR, 'mill_thread_mill_int_main.svg'))
            self.image_list['thread_mill_detail_image'].set_from_file(os.path.join(GLADE_DIR, 'mill_thread_mill_int_detail.svg'))

            # turn External DROs OFF
            ##self.thread_mill_ext_dro_list['thread_mill_ext_x_dro'].set_visible(False)
            ##self.thread_mill_ext_dro_list['thread_mill_ext_y_dro'].set_visible(False)
            self.thread_mill_ext_dro_list['thread_mill_ext_z_start_dro'].set_visible(False)
            self.thread_mill_ext_dro_list['thread_mill_ext_z_end_dro'].set_visible(False)
            self.thread_mill_ext_dro_list['thread_mill_ext_major_dia_dro'].set_visible(False)
            self.thread_mill_ext_dro_list['thread_mill_ext_minor_dia_dro'].set_visible(False)
            self.thread_mill_ext_dro_list['thread_mill_ext_doc_dro'].set_visible(False)
            self.thread_mill_ext_dro_list['thread_mill_ext_passes_dro'].set_visible(False)
            self.thread_mill_ext_dro_list['thread_mill_ext_pitch_dro'].set_visible(False)
            self.thread_mill_ext_dro_list['thread_mill_ext_tpu_dro'].set_visible(False)

            # turn Internal DROs ON
            ##self.thread_mill_int_dro_list['thread_mill_int_x_dro'].set_visible(True)
            ##self.thread_mill_int_dro_list['thread_mill_int_y_dro'].set_visible(True)
            self.thread_mill_int_dro_list['thread_mill_int_z_start_dro'].set_visible(True)
            self.thread_mill_int_dro_list['thread_mill_int_z_end_dro'].set_visible(True)
            self.thread_mill_int_dro_list['thread_mill_int_major_dia_dro'].set_visible(True)
            self.thread_mill_int_dro_list['thread_mill_int_minor_dia_dro'].set_visible(True)
            self.thread_mill_int_dro_list['thread_mill_int_doc_dro'].set_visible(True)
            self.thread_mill_int_dro_list['thread_mill_int_passes_dro'].set_visible(True)
            self.thread_mill_int_dro_list['thread_mill_int_pitch_dro'].set_visible(True)
            self.thread_mill_int_dro_list['thread_mill_int_tpu_dro'].set_visible(True)

            ## these conv_DROs are also changed in on_conver_notebook_switch_page
            #self.conv_dro_list['conv_rough_sfm_dro'].set_sensitive(False)

            self.conv_thread_mill_ext_int = 'internal'

        else:  #self.conv_thread_mill_ext_int == 'internal':
            self.set_image('thread_mill_ext_int_btn_image', 'thread_ext_button.jpg')
            self.image_list['thread_mill_main_image'].set_from_file(os.path.join(GLADE_DIR, 'mill_thread_mill_ext_main.svg'))
            self.image_list['thread_mill_detail_image'].set_from_file(os.path.join(GLADE_DIR, 'mill_thread_mill_ext_detail.svg'))

            # turn Internal DROs OFF
            ##self.thread_mill_int_dro_list['thread_mill_int_x_dro'].set_visible(False)
            ##self.thread_mill_int_dro_list['thread_mill_int_y_dro'].set_visible(False)
            self.thread_mill_int_dro_list['thread_mill_int_z_start_dro'].set_visible(False)
            self.thread_mill_int_dro_list['thread_mill_int_z_end_dro'].set_visible(False)
            self.thread_mill_int_dro_list['thread_mill_int_major_dia_dro'].set_visible(False)
            self.thread_mill_int_dro_list['thread_mill_int_minor_dia_dro'].set_visible(False)
            self.thread_mill_int_dro_list['thread_mill_int_doc_dro'].set_visible(False)
            self.thread_mill_int_dro_list['thread_mill_int_passes_dro'].set_visible(False)
            self.thread_mill_int_dro_list['thread_mill_int_pitch_dro'].set_visible(False)
            self.thread_mill_int_dro_list['thread_mill_int_tpu_dro'].set_visible(False)

            # turn External DROs ON
            ##self.thread_mill_ext_dro_list['thread_mill_ext_x_dro'].set_visible(True)
            ##self.thread_mill_ext_dro_list['thread_mill_ext_y_dro'].set_visible(True)
            self.thread_mill_ext_dro_list['thread_mill_ext_z_start_dro'].set_visible(True)
            self.thread_mill_ext_dro_list['thread_mill_ext_z_end_dro'].set_visible(True)
            self.thread_mill_ext_dro_list['thread_mill_ext_major_dia_dro'].set_visible(True)
            self.thread_mill_ext_dro_list['thread_mill_ext_minor_dia_dro'].set_visible(True)
            self.thread_mill_ext_dro_list['thread_mill_ext_doc_dro'].set_visible(True)
            self.thread_mill_ext_dro_list['thread_mill_ext_passes_dro'].set_visible(True)
            self.thread_mill_ext_dro_list['thread_mill_ext_pitch_dro'].set_visible(True)
            self.thread_mill_ext_dro_list['thread_mill_ext_tpu_dro'].set_visible(True)

            ## these conv_DROs are also changed in on_conv_notebook_switch_page
            #self.conv_dro_list['conv_rough_sfm_dro'].set_sensitive(False)

            self.conv_thread_mill_ext_int = 'external'
        self.load_title_dro()
        # stuff dros with new values for int or ext
        if self.conv_thread_mill_ext_int == 'external':
            self.thread_mill_ext_dro_list['thread_mill_ext_doc_dro'].grab_focus()
        else:
            self.thread_mill_int_dro_list['thread_mill_int_doc_dro'].grab_focus()
        self.on_thread_chart_changed(self.builder.get_object('thread_combobox'))


    def on_thread_mill_ext_int_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.on_thread_mill_ext_int_set_state()


    def on_thread_chart_changed(self, widget, data=None):
        # get active entry, populate DROs
        model = widget.get_model()
        active_text = widget.get_active()
        if active_text == -1:  # catch when the default empty cell is active
            return
        thread_str = model[active_text][1].strip()
        if len(thread_str) == 0 or thread_str == THREAD_CUSTOM_DELIMITER or thread_str == THREAD_TORMACH_DELIMITER:
            # empty or delimiter string selected, do nothing
            return
        # parse space delimited string in text
        tpu, ext_major, ext_minor, int_major, int_minor = [x.strip() for x in thread_str.split(',') if x.strip()]

        tpu = float(tpu)
        pitch = 1 / tpu

        # use external or internal diameters as required to set DROs
        if self.conv_thread_mill_ext_int == 'external':
            major_diameter = float(ext_major)
            minor_diameter = float(ext_minor)
            self.thread_mill_ext_dro_list['thread_mill_ext_major_dia_dro'].set_text(self.dro_long_format % major_diameter)
            self.thread_mill_ext_dro_list['thread_mill_ext_minor_dia_dro'].set_text(self.dro_long_format % minor_diameter)
            self.thread_mill_ext_dro_list['thread_mill_ext_tpu_dro'].set_text(self.dro_medium_format % tpu)
            self.thread_mill_ext_dro_list['thread_mill_ext_pitch_dro'].set_text(self.dro_long_format % pitch)
        else:
            major_diameter = float(int_major)
            minor_diameter = float(int_minor)
            self.thread_mill_int_dro_list['thread_mill_int_major_dia_dro'].set_text(self.dro_long_format % major_diameter)
            self.thread_mill_int_dro_list['thread_mill_int_minor_dia_dro'].set_text(self.dro_long_format % minor_diameter)
            self.thread_mill_int_dro_list['thread_mill_int_tpu_dro'].set_text(self.dro_medium_format % tpu)
            self.thread_mill_int_dro_list['thread_mill_int_pitch_dro'].set_text(self.dro_long_format % pitch)


    # External
    def on_thread_mill_ext_x_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_ext_dro_list['thread_mill_ext_y_dro'].grab_focus()
        return

    def on_thread_mill_ext_y_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_ext_dro_list['thread_mill_ext_z_start_dro'].grab_focus()
        return

    def on_thread_mill_ext_z_start_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_ext_dro_list['thread_mill_ext_z_end_dro'].grab_focus()
        return

    def on_thread_mill_ext_z_end_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_ext_dro_list['thread_mill_ext_major_dia_dro'].grab_focus()
        return

    def on_thread_mill_ext_major_dia_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_ext_dro_list['thread_mill_ext_minor_dia_dro'].grab_focus()
        return

    def on_thread_mill_ext_minor_dia_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_ext_dro_list['thread_mill_ext_passes_dro'].grab_focus()
        return

    def on_thread_mill_ext_passes_dro_activate(self, widget, data=None):
        (valid, num_passes, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%d' % num_passes)

        # passes is valid, so check major and minor, then calculate doc
        (valid, major_dia, error_msg) = self.conversational.validate_param(self.thread_mill_ext_dro_list['thread_mill_ext_major_dia_dro'])
        if not valid:
            self.thread_mill_ext_dro_list['thread_mill_ext_major_dia_dro'].grab_focus()
            # return <-- ?
        else:
            major_radius = major_dia / 2

        (valid, minor_dia, error_msg) = self.conversational.validate_param(self.thread_mill_ext_dro_list['thread_mill_ext_minor_dia_dro'])
        if not valid:
            self.thread_mill_ext_dro_list['thread_mill_ext_minor_dia_dro'].grab_focus()
        else:
            minor_radius = minor_dia / 2

        thread_range = math.fabs(major_radius - minor_radius)
        area_range = (thread_range ** 2) / math.sqrt(3)
        area_doc = area_range / num_passes
        doc = math.sqrt(area_doc * math.sqrt(3))

        self.thread_mill_ext_dro_list['thread_mill_ext_doc_dro'].set_text(self.dro_long_format % doc)

        self.thread_mill_ext_dro_list['thread_mill_ext_doc_dro'].grab_focus()
        return

    def on_thread_mill_ext_doc_dro_activate(self, widget, data=None):
        (valid, doc_requested, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % doc_requested)
        # doc is valid, so check major and minor, then calculate passes
        (valid, major_dia, error_msg) = self.conversational.validate_param(self.thread_mill_ext_dro_list['thread_mill_ext_major_dia_dro'])
        if not valid:
            self.thread_mill_ext_dro_list['thread_mill_ext_major_dia_dro'].grab_focus()
            # return <-- ?
        else:
            major_radius = major_dia / 2

        (valid, minor_dia, error_msg) = self.conversational.validate_param(self.thread_mill_ext_dro_list['thread_mill_ext_minor_dia_dro'])
        if not valid:
            self.thread_mill_ext_dro_list['thread_mill_ext_minor_dia_dro'].grab_focus()
        else:
            minor_radius = minor_dia / 2

        area_doc_requested = (doc_requested ** 2) / math.sqrt(3)
        thread_range = math.fabs(major_radius - minor_radius)
        area_range = (thread_range ** 2) / math.sqrt(3)
        num_passes = int(round(area_range / area_doc_requested))
        if num_passes > 0:
            area_adjusted = area_range / num_passes
            doc_adjusted = math.sqrt(area_adjusted * math.sqrt(3))

            self.thread_mill_ext_dro_list['thread_mill_ext_passes_dro'].set_text(self.dro_short_format % num_passes)
            (valid, number, error_msg) = self.conversational.validate_param(self.thread_mill_ext_dro_list['thread_mill_ext_passes_dro'])

            widget.set_text('%s' % self.dro_long_format % doc_adjusted)

            self.thread_mill_ext_dro_list['thread_mill_ext_pitch_dro'].grab_focus()
        else:  # error, num passes < 1
            error_msg = 'This depth of cut produces less than one pass, please set to %s or less' % self.dro_long_format % thread_range
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            mill_conversational.raise_alarm(widget)

        return

    def on_thread_mill_ext_pitch_dro_activate(self, widget, data=None):
        (valid, pitch, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % pitch)

        if pitch > 0:
            tpu = 1 / pitch
        else:
            tpu = 0
        self.thread_mill_ext_dro_list["thread_mill_ext_tpu_dro"].set_text(self.dro_medium_format % tpu)

        self.thread_mill_ext_dro_list['thread_mill_ext_tpu_dro'].grab_focus()
        return

    def on_thread_mill_ext_tpu_dro_activate(self, widget, data=None):
        (valid, tpu, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_medium_format % tpu)

        pitch = 1 / tpu
        self.thread_mill_ext_dro_list["thread_mill_ext_pitch_dro"].set_text(self.dro_long_format % pitch)

        self.thread_mill_ext_dro_list['thread_mill_ext_z_start_dro'].grab_focus()
        return


    # Internal
    def on_thread_mill_int_x_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_int_dro_list['thread_mill_int_y_dro'].grab_focus()
        return

    def on_thread_mill_int_y_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_int_dro_list['thread_mill_int_z_start_dro'].grab_focus()
        return

    def on_thread_mill_int_z_start_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_int_dro_list['thread_mill_int_z_end_dro'].grab_focus()
        return

    def on_thread_mill_int_z_end_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_int_dro_list['thread_mill_int_major_dia_dro'].grab_focus()
        return

    def on_thread_mill_int_major_dia_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_int_dro_list['thread_mill_int_minor_dia_dro'].grab_focus()
        return

    def on_thread_mill_int_minor_dia_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.thread_mill_int_dro_list['thread_mill_int_passes_dro'].grab_focus()
        return

    def on_thread_mill_int_passes_dro_activate(self, widget, data=None):
        (valid, num_passes, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%d' % num_passes)

        # passes is valid, so check major and minor, then calculate doc
        (valid, major_dia, error_msg) = self.conversational.validate_param(self.thread_mill_int_dro_list['thread_mill_int_major_dia_dro'])
        if not valid:
            self.thread_mill_int_dro_list['thread_mill_int_major_dia_dro'].grab_focus()
            # return <-- ?
        else:
            major_radius = major_dia / 2

        (valid, minor_dia, error_msg) = self.conversational.validate_param(self.thread_mill_int_dro_list['thread_mill_int_minor_dia_dro'])
        if not valid:
            self.thread_mill_int_dro_list['thread_mill_int_minor_dia_dro'].grab_focus()
        else:
            minor_radius = minor_dia / 2

        thread_range = math.fabs(major_radius - minor_radius)
        area_range = (thread_range ** 2) / math.sqrt(3)
        area_doc = area_range / num_passes
        doc = math.sqrt(area_doc * math.sqrt(3))

        self.thread_mill_int_dro_list['thread_mill_int_doc_dro'].set_text(self.dro_long_format % doc)

        self.thread_mill_int_dro_list['thread_mill_int_doc_dro'].grab_focus()
        return

    def on_thread_mill_int_doc_dro_activate(self, widget, data=None):
        (valid, doc_requested, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % doc_requested)

        (valid, major_dia, error_msg) = self.conversational.validate_param(self.thread_mill_int_dro_list['thread_mill_int_major_dia_dro'])
        if not valid:
            self.thread_mill_int_dro_list['thread_mill_int_major_dia_dro'].grab_focus()
            # return <-- ?
        else:
            major_radius = major_dia / 2

        (valid, minor_dia, error_msg) = self.conversational.validate_param(self.thread_mill_int_dro_list['thread_mill_int_minor_dia_dro'])
        if not valid:
            self.thread_mill_int_dro_list['thread_mill_int_minor_dia_dro'].grab_focus()
        else:
            minor_radius = minor_dia / 2

        area_doc_requested = (doc_requested ** 2) / math.sqrt(3)
        thread_range = math.fabs(major_radius - minor_radius)
        area_range = (thread_range ** 2) / math.sqrt(3)
        num_passes = int(round(area_range / area_doc_requested))
        area_adjusted = area_range / num_passes
        doc_adjusted = math.sqrt(area_adjusted * math.sqrt(3))

        self.thread_mill_int_dro_list['thread_mill_int_passes_dro'].set_text(self.dro_short_format % num_passes)
        (valid, number, error_msg) = self.conversational.validate_param(self.thread_mill_int_dro_list['thread_mill_int_passes_dro'])

        widget.set_text('%s' % self.dro_long_format % doc_adjusted)

        self.thread_mill_int_dro_list['thread_mill_int_pitch_dro'].grab_focus()
        return

    def on_thread_mill_int_pitch_dro_activate(self, widget, data=None):
        (valid, pitch, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % pitch)
        if pitch > 0:
            tpu = 1 / pitch
        else:
            tpu = 0
        self.thread_mill_int_dro_list["thread_mill_int_tpu_dro"].set_text(self.dro_medium_format % tpu)

        self.thread_mill_int_dro_list['thread_mill_int_tpu_dro'].grab_focus()
        return

    def on_thread_mill_int_tpu_dro_activate(self, widget, data=None):
        (valid, tpu, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_medium_format % tpu)

        pitch = 1 / tpu
        self.thread_mill_int_dro_list["thread_mill_int_pitch_dro"].set_text(self.dro_long_format % pitch)

        self.thread_mill_int_dro_list['thread_mill_int_z_start_dro'].grab_focus()
        return

    # Internal and External

    # these two radio buttons are a group
    def on_thread_mill_right_radiobutton_toggled(self, widget, data=None):
        if widget.get_active():
            self.thread_mill_rhlh = "right"
            self.window.set_focus(None)

    def on_thread_mill_left_radiobutton_toggled(self, widget, data=None):
        if widget.get_active():
            self.thread_mill_rhlh = "left"
            self.window.set_focus(None)


    # -------------------------------------------------------------------------------------------------
    # Conversational
    # Engrave DRO handlers
    # -------------------------------------------------------------------------------------------------
    """
    def on_engrave_font_tview_click(self, treeview, event):  # capures mouse click to select row, updates sample
        x = int(event.x)
        y = int(event.y)
        model = treeview.get_model()
        pthinfo = treeview.get_path_at_pos(x, y)
        font_row = pthinfo[0][0]
        self.engrave_font_pf= ENGRAVING_FONTS_DIR + self.font_file_list[font_row]
        (ef_name, ef_family) = self.get_ttfont_name(self.engrave_font_pf)

        engrave_text = self.engrave_dro_list['engrave_text_dro'].get_text()
        #engrave_text = engrave_text.set_markup('<span font_family="%s" font_desc="%s 20">%s</span>' % (ef_family, ef_name, engrave_text))
        #self.engrave_dro_list['engrave_text_dro'].set_text(engrave_text)

        #font_description = pango.FontDescription(ef_family + ' ' + ef_name + 'normal 22')
        ##font_description = pango.FontDescription(ef_name + ' 24')
        ##self.engrave_dro_list['engrave_text_dro'].modify_font(font_description)

        if engrave_text == "":
            engrave_text = "Please enter text above"
            self.engrave_sample_label.set_markup('<span font_family="%s" font_desc="%s 12">%s</span>' % (ef_family, ef_name, engrave_text))
        else:
            self.engrave_sample_label.set_markup('<span font_family="%s" font_desc="%s 26">%s</span>' % (ef_family, ef_name, engrave_text))

        return
    """
    def conv_engrave_switch_page(self):
        self.engrave_dro_list['engrave_sn_start_dro'].set_text('')
        return

    def on_engrave_sn_start_button_release(self, widget, data=None):
        current_sn = ''
        try:
            current_sn = self.redis.hget('machine_prefs', 'current_engraving_sn')
        except:
            pass
        self.engrave_dro_list['engrave_sn_start_dro'].set_text(current_sn)
        self.engrave_dro_list['engrave_sn_start_dro'].select_region(0,-1)
        return

    def ef_scroll_adjust(self, row):
        # get var list from vertical scroll bar
        adj = self.scrolled_window_engrave_font.get_vadjustment()

        unitsperrow = (adj.upper - adj.lower) / self.ef_num_rows
        centerofpage = adj.page_size / 2
        centerofrow = unitsperrow / 2
        cofcurrentrow = (row * unitsperrow) + centerofrow
        scroll_offset = cofcurrentrow - centerofpage

        if scroll_offset < 0:
            scroll_offset = 0
        elif scroll_offset > (adj.upper - adj.page_size):
            scroll_offset = (adj.upper - adj.page_size)

        adj.set_value(scroll_offset)


    def on_engrave_text_dro_activate(self, widget, data=None):
        # the 'normal' validate allows for empty text...
        (valid, engrave_text, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return

        # an empty engrave text is ok, if empty check the serial number
        # if that is also empty - not ok. On the second test 'validate_text'
        # is called which won't allow empty text.
        sn_text = self.engrave_dro_list['engrave_sn_start_dro'].get_text()
        if len(sn_text) == 0:
            (valid, engrave_text, error_msg) = self.conversational.validate_text(widget)
            if not valid:
                self.error_handler.write('Enter either Text and/or a Serial Number', ALARM_LEVEL_LOW)
                return
        mill_conversational.raise_alarm(widget, False)
        mill_conversational.raise_alarm(self.engrave_dro_list['engrave_sn_start_dro'], False)

        self.engrave_sample_update()
        self.engrave_dro_list['engrave_height_dro'].grab_focus()
        return

    def on_engrave_set_font(self, font_file):
        (family, name) = self.get_ttfont_name(font_file)
        for row in self.engrave_font_liststore:
            font_info = row[0]
            if name in font_info:
                try:
                    iter_item = getattr(row,'iter')
                    selection = self.engrave_font_treeview.get_selection()
                    selection.select_iter(iter_item)
                    path = getattr(row,'path')
                    self.ef_scroll_adjust(path[0]) # this is a single tuple
                    self.engrave_sample_update()
                    self.engrave_font_pf = font_file
                except:
                    print 'Exception ocurred in on_engrave_set_font'
                break
        return

    def on_engrave_font_tview_cursor_changed(self, treeview):
        # on cursor position change, center cursor in window, redraw sample
        cursor_actv_list, tvcolumnobj = treeview.get_cursor()
        row = cursor_actv_list[0]  # get first and only selected row

        # remember the font row for configuring the font selector next time
        self.engrave_font_row = row
        # activate new font
        self.engrave_font_pf = os.path.join(ENGRAVING_FONTS_DIR, self.font_file_list[row])
        (ef_name, ef_family) = self.get_ttfont_name(self.engrave_font_pf)

        # center font selection in window
        self.ef_scroll_adjust(row)
        self.engrave_sample_update()
        return

    def engrave_sample_update(self):
        # update font sample label
        engrave_text = self.engrave_dro_list['engrave_text_dro'].get_text()
        (ef_name, ef_family) = self.get_ttfont_name(self.engrave_font_pf)

        if self.engrave_just == 'right':
            self.engrave_sample_label.set_alignment(xalign=1, yalign=0.5)
        elif self.engrave_just == 'center':
            self.engrave_sample_label.set_alignment(xalign=0.5, yalign=0.5)
        else:  # left
            self.engrave_sample_label.set_alignment(xalign=0.0, yalign=0.5)

        if engrave_text == "":
            engrave_text = "Please enter text above"
            self.engrave_sample_label.set_markup('<span font_family="%s" font_desc="%s 12">%s</span>' % (ef_family, ef_name, engrave_text))
        else:
            self.engrave_sample_label.set_markup('<span font_family="%s" font_desc="%s 26">%s</span>' % (ef_family, ef_name, engrave_text))
            self.engrave_dro_list['engrave_height_dro'].grab_focus()
        return


    def on_engrave_x_base_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.engrave_dro_list['engrave_y_base_dro'].grab_focus()
        return

    def on_engrave_y_base_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.engrave_dro_list['engrave_z_start_dro'].grab_focus()
        return

    def on_engrave_z_start_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.engrave_dro_list['engrave_z_doc_dro'].grab_focus()
        return

    def on_engrave_height_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.engrave_dro_list['engrave_x_base_dro'].grab_focus()
        return

    def on_engrave_z_doc_dro_activate(self, widget, data=None):
        (valid, number, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text('%s' % self.dro_long_format % number)
        self.engrave_dro_list['engrave_text_dro'].grab_focus()
        return

    def on_engrave_sn_start_dro_focus_in_event(self, widget, data=None):
        current_number = widget.get_text()
        if len(current_number) > 0:
            return
        try:
            current_sn = self.redis.hget('machine_prefs', 'current_engraving_sn')
            current_text = widget.get_text()
            current_text_length = len(current_text)
            current_sn_length = len(current_sn)
            while current_sn_length < current_text_length:
                current_sn = "0%s" % current_sn
                current_sn_length += 1
            widget.set_text(current_sn)
        except:
            pass
        return

    def on_engrave_sn_start_dro_activate(self, widget, data=None):
        (valid, number_as_text, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        text = number_as_text if number_as_text is not None else ''
        try:
            if len(text) > 0:
                self.redis.hset('machine_prefs', 'current_engraving_sn', text)
        except:
            pass
        widget.set_text(text)

        # if the serial number is empty that's ok. Test for on empty text in engrave text
        # if both are empty an error is thrown through 'validate_text'
        if len(text) > 0:
            self.conversational.validate_param(self.engrave_dro_list['engrave_text_dro'])
        else:
            text = self.engrave_dro_list['engrave_text_dro'].get_text()
            if text == '':
                valid,t,error = self.conversational.validate_text(widget)
                error = '%s: Enter either Text and/or a Serial Number' % error
                self.error_handler.write(error, ALARM_LEVEL_LOW)
                return
        mill_conversational.raise_alarm(widget, False)
        mill_conversational.raise_alarm(self.engrave_dro_list['engrave_text_dro'], False)
        self.engrave_dro_list['engrave_height_dro'].grab_focus()
        return

    def on_engrave_sn_start_visibility_notify(self, widget, event, data = None):
        # set the current SN toolip here
        if event.state == gtk.gdk.VISIBILITY_UNOBSCURED:
            # set the tooltip to the current SN
            try:
                current_sn = self.redis.hget('machine_prefs', 'current_engraving_sn')
                current_text = widget.get_text()
                current_text_length = len(current_text)
                current_sn_length = len(current_sn)
                while current_sn_length < current_text_length:
                    current_sn = "0%s" % current_sn
                    current_sn_length += 1
                widget.set_tooltip_text('Current SN: %s' % (current_sn))
            except:
                pass
        return

    # these three radio buttons are a group
    def on_engrave_left_radiobutton_toggled(self, widget, data=None):
        if widget.get_active():
            self.engrave_just = "left"
            self.engrave_sample_update()
            self.window.set_focus(None)

    def on_engrave_center_radiobutton_toggled(self, widget, data=None):
        if widget.get_active():
            self.engrave_just = "center"
            self.engrave_sample_update()
            self.window.set_focus(None)

    def on_engrave_right_radiobutton_toggled(self, widget, data=None):
        if widget.get_active():
            self.engrave_just = "right"
            self.engrave_sample_update()
            self.window.set_focus(None)



    # -------------------------------------------------------------------------------------------------
    # end of conversational tab callbacks
    # -------------------------------------------------------------------------------------------------


    # -------------------------------------------------------------------------------------------------
    # probe callbacks
    # -------------------------------------------------------------------------------------------------


    # -------------------------------------------------------------------------------------------------
    # x/y probing
    # -------------------------------------------------------------------------------------------------
			
    def on_probe_find_corner_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_corner(self)

    def on_probe_x_plus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_x_plus(self)

    def on_probe_origin_x_plus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_x_plus_origin(self)

    def on_probe_x_minus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_x_minus(self)

    def on_probe_origin_x_minus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_x_minus_origin(self)

    def on_probe_y_plus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_y_plus(self)

    def on_probe_y_plus_a_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_y_plus_a(self)

    def on_probe_y_plus_b_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_y_plus_b(self)

    def on_probe_y_plus_c_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_y_plus_c(self)

    def on_probe_origin_y_plus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_y_plus_origin(self)

    def on_probe_y_minus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_y_minus(self)

    def on_probe_origin_y_minus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_y_minus_origin(self)

    def on_probe_z_minus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_z_minus(self)

    def on_probe_origin_z_minus_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_z_minus_origin(self)


    # -------------------------------------------------------------------------------------------------
    # Rect/Circ Boss probing
    # -------------------------------------------------------------------------------------------------

    def on_probe_find_rect_boss_center_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_rect_boss_center(self)

    def on_probe_find_circ_boss_center_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_circ_boss_center(self)


    # -------------------------------------------------------------------------------------------------
    # Rect/Circ Pocket probing
    # -------------------------------------------------------------------------------------------------

    def on_probe_find_pocket_center_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_pocket_center(self)

    def on_probe_find_pocket_x_center_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_pocket_x_center(self)

    def on_probe_find_pocket_y_center_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_pocket_y_center(self)

    def on_probe_a_axis_center_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_a_axis_center(self)

    # -------------------------------------------------------------------------------------------------
    # z probing
    # -------------------------------------------------------------------------------------------------


    def on_probe_set_work_offset_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        probing.find_work_z(self)

    def issue_tool_offset_command(self, axis, offset_register, value):
        g10_command = "G10 L1 P%d %s%f" %(offset_register, axis, value)
        self.issue_mdi(g10_command)
        self.command.wait_complete()

    # -------------------------------------------------------------------------------------------------
    # probe/ets setup
    # -------------------------------------------------------------------------------------------------

    def on_probe_set_gauge_ref_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        if self.status.tool_in_spindle != -1:
            self.error_handler.write("Tool 0 (empty spindle) must be active before setting the reference surface height.  Remove tool from spindle and change active tool to tool 0 before continuing", ALARM_LEVEL_MEDIUM)
            return
        self.probe_setup_reference_surface = self.status.position[2]


    def on_ets_height_dro_activate(self, widget, data=None):
        (valid, value, error_msg) = self.conversational.validate_param(widget)
        if not valid:
            self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            return
        widget.set_text(self.dro_long_format % value)
        # store this value in machine setup untis (inches) at all times.
        self.ets_height = value/self.get_linear_scale()
        self.redis.hset('machine_prefs', 'setter_height', self.ets_height)
        widget.masked = False
        self.window.set_focus(None)

    def on_probe_set_probe_length_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        if self.status.tool_in_spindle != 99:
            self.error_handler.write("Tool 99 (probe tool) must be active before setting the reference surface height.  Change active tool to tool 99 before continuing", ALARM_LEVEL_MEDIUM)
            return
        try:
            float(self.probe_setup_reference_surface)
        except:
            self.error_handler.write('Reference surface height not set - using work offset Z zero for reference surface', ALARM_LEVEL_LOW)
        probing.move_and_set_probe_length(self)



    # -------------------------------------------------------------------------------------------------
    # conversational helpers
    # -------------------------------------------------------------------------------------------------

    def save_conv_title(self, key):
        if self.redis.hexists('machine_prefs',key):
            value = self.conv_dro_list['conv_title_dro'].get_text()
            self.redis.hset('machine_prefs',key,value)
        else:
            print 'save_conv_title - could not find %s' % key

    def save_conv_parameters(self, dro_list):
        # loop through conv dro list and save values to redis
        for name, dro in self.conv_dro_list.iteritems():
            val = dro.get_text()
            self.redis.hset('conversational', name, val)
        for name, dro in dro_list.iteritems():
            val = dro.get_text()
            self.redis.hset('conversational', name, val)
        return

    def restore_conv_parameters(self):
        conv_dict = self.redis.hgetall('conversational')
        for dro_name , val in conv_dict.iteritems():
            try:
                if 'conv' in dro_name:
                    self.conv_dro_list[dro_name].set_text(val)
                    self.current_normal_z_feed_rate = self.conv_dro_list['conv_z_feed_dro'].get_text()
                if 'face' in dro_name:
                    self.face_dro_list[dro_name].set_text(val)
                if 'profile' in dro_name:
                    self.profile_dro_list[dro_name].set_text(val)
                if 'pocket_rect' in dro_name:
                    self.pocket_rect_dro_list[dro_name].set_text(val)
                if 'pocket_circ' in dro_name:
                    self.pocket_circ_dro_list[dro_name].set_text(val)
                if 'pattern_circular' in dro_name:
                    self.drill_circular_dro_list[dro_name].set_text(val)
                if 'drill' in dro_name:
                    self.drill_dro_list[dro_name].set_text(val)
                if 'tap' in dro_name:
                    self.tap_dro_list[dro_name].set_text(val)
                if 'thread_mill_ext' in dro_name:
                    self.thread_mill_ext_dro_list[dro_name].set_text(val)
                if 'thread_mill_int' in dro_name:
                    self.thread_mill_int_dro_list[dro_name].set_text(val)
                if 'engrave' in dro_name:
                    self.engrave_dro_list[dro_name].set_text(val)
                if 'scan' in dro_name:
                    self.scanner_scan_dro_list[dro_name].set_text(val)
            except:
                pass
        return

    def ini_float(self, ini_section, ini_var, def_val):
        val = def_val
        try:
            val =  float(self.inifile.find(ini_section, ini_var))
        except TypeError:
            pass
        return val

    def ini_int(self, ini_section, ini_var):
        val = 0
        try:
            val =  int(self.inifile.find(ini_section, ini_var))
        except TypeError:
            pass
        return val

    def ini_flag(self, ini_section, ini_var, def_val):
        # return True for YES in INI file, def_val for anything else
        val = def_val
        val_str =  self.inifile.find(ini_section, ini_var)
        if val_str != None:
            if val_str.upper() == "YES":
                val = True
        return val

    def enable_home_switch(self, axis_index, enable_flag):
        print 'enable home axis %d, flag %d' % (axis_index, enable_flag)
        # if enable_flag is False sets home_offset, search velocity and latch velocity to 0.0
        # else sets all to INI file values
        # 0 for X, 1 for Y, 2 for Z
        if axis_index == 0:
            axis_N = "AXIS_0"
        elif axis_index == 1:
            axis_N = "AXIS_1"
        elif axis_index == 2:
            axis_N = "AXIS_2"
        else:
            self.error_handler.write("invalid axis index '%d' for enable_home_switch()" % axis_index, ALARM_LEVEL_LOW)
            return

        home = self.ini_float(axis_N, "HOME", 0.0)
        if (enable_flag == True):
            home_offset = self.ini_float(axis_N, "HOME_OFFSET", 0.0)
            home_search_vel = self.ini_float(axis_N, "HOME_SEARCH_VEL", 0.0)
            home_latch_vel = self.ini_float(axis_N, "HOME_LATCH_VEL", 0.0)
        else:
            home_offset = 0.0
            home_search_vel = 0.0
            home_latch_vel = 0.0
        home_final_vel = self.ini_float(axis_N, "HOME_FINAL_VEL", -1)
        home_use_index = self.ini_flag(axis_N, "HOME_USE_INDEX", False)
        home_ignore_limits = self.ini_flag(axis_N, "HOME_IGNORE_LIMITS", False)
        home_home_is_shared = self.ini_flag(axis_N, "HOME_IS_SHARED", 0)
        home_sequence = self.ini_flag(axis_N, "HOME_SEQUENCE", 0)
        volatile_home = self.ini_flag(axis_N, "VOLATILE_HOME", 0)
        locking_indexer = self.ini_flag(axis_N, "LOCKING_INDEXER", 0)

        self.command.set_homing_params(axis_index, home, home_offset, home_final_vel, home_search_vel,
                                       home_latch_vel, home_use_index, home_ignore_limits,
                                       home_home_is_shared, home_sequence, volatile_home,
                                       locking_indexer)

    def on_disable_home_switches_checkbutton_toggled(self, widget, data=None):
        self.home_switches_enabled = not widget.get_active()
        self.hal["home-switch-enable"] = self.home_switches_enabled
        self.redis.hset('machine_prefs', 'home_switches_enabled', self.home_switches_enabled)
        self.window.set_focus(None)
        if self.home_switches_enabled:
            self.enable_home_switch(0, True)
            self.enable_home_switch(1, True)
            self.enable_home_switch(2, True)
        else:
            self.enable_home_switch(0, False)
            self.enable_home_switch(1, False)
            self.enable_home_switch(2, False)

    def set_4th_axis_homing_parameters(self, enable_flag):
        axis_N = 'AXIS_3'
        home = self.ini_float(axis_N, "HOME", 0.0)
        if (enable_flag == True):
            # TODO: put these values in INI as HOME_xxxxxx_HOMING_KIT
            home_offset = self.ini_float(axis_N, "HOME_OFFSET_HOMING_KIT", 0.0)
            home_search_vel = self.ini_float(axis_N, "HOME_SEARCH_VEL_HOMING_KIT", 5.0)
            home_latch_vel = self.ini_float(axis_N, "HOME_LATCH_VEL_HOMING_KIT", 0.5)
        else:
            # these set to zero means 'set home where it is now' - no motion
            home_offset = 0.0
            home_search_vel = 0.0
            home_latch_vel = 0.0
        home_final_vel = self.ini_float(axis_N, "HOME_FINAL_VEL", -1)
        home_use_index = self.ini_flag(axis_N, "HOME_USE_INDEX", False)
        home_ignore_limits = self.ini_flag(axis_N, "HOME_IGNORE_LIMITS", False)
        home_home_is_shared = self.ini_flag(axis_N, "HOME_IS_SHARED", 0)
        home_sequence = self.ini_flag(axis_N, "HOME_SEQUENCE", 0)
        volatile_home = self.ini_flag(axis_N, "VOLATILE_HOME", 0)
        locking_indexer = self.ini_flag(axis_N, "LOCKING_INDEXER", 0)

        self.command.set_homing_params(3, home, home_offset, home_final_vel, home_search_vel,
                                       home_latch_vel, home_use_index, home_ignore_limits,
                                       home_home_is_shared, home_sequence, volatile_home,
                                       locking_indexer)

    # -------------------------------------------------------------------------------------------------
    # Alarms page
    # -------------------------------------------------------------------------------------------------

    def on_netbios_name_activate(self, widget, data=None):
        nbentry_text = validate_netbios_name(widget.get_text())
        # if empty, fill in existing name
        if nbentry_text == '':
            nbentry_text = self.netbios_name
        # stuff the result back into the text entry
        widget.set_text(nbentry_text)
        # if changed, set the new NetBIOS name
        if nbentry_text != self.netbios_name:
            self.netbios_name = nbentry_text
            set_netbios_name(netbios_name_conf_file, nbentry_text)

    def on_zero_height_gauge_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.hal['hg-set-zero-offset'] = True;
        #self.dro_list['height_gauge_dro'].set_text(self.dro_long_format % 0.0)

    def on_clear_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.error_handler.clear_history()

    def on_update_button_release_event(self, widget, data=None):
        if not self.check_button_permissions(widget): return
        self.software_update()


    # ----------------------------------------
    # helpers
    # ----------------------------------------




    def highlight_offsets_treeview_row(self):
        tool_num = self.status.tool_in_spindle
        if tool_num > 0:
            self.treeselection.select_path(tool_num - 1)

    def clear_job_liststore(self):
        self.job_liststore.clear()
        for id_cnt  in range(1, JOB_TABLE_ROWS + 1):
                    self.job_liststore.append([id_cnt, '', '', '', 0, 0])

    def get_current_notebook_page(self):
        # page number is dynamic, and depends on whether the ATC or scanner are enabled
        # the first 6 pages don't change, but ATC, SCANNER, and STATUS can have different vals
        # depending on what is currently enabled.
        page_num = self.notebook.get_current_page()
        if page_num <= 5:
            return page_num
        else:
            page = self.notebook.get_nth_page(page_num)
            text = self.notebook.get_tab_label_text(page)
            if text == None: return MILL_STATUS_PAGE
            elif 'ATC' in text: return ATC_PAGE
            elif 'Scanner' in text: return CNC_SCANNER_PAGE
            elif 'Camera' in text: return CNC_SCANNER_PAGE
            elif 'Injector' in text: return INJECTOR_PAGE


    def hide_notebook_tabs(self):
        for i in range(1, MILL_STATUS_PAGE):
            page = self.notebook.get_nth_page(i)
            page.hide()
        # only hide the alarms tab if no alarms are active
        if not self.error_handler.get_alarm_active():
            page = self.notebook.get_nth_page(MILL_STATUS_PAGE)
            page.hide()

    def show_enabled_notebook_tabs(self, data=None):
        for i in range(1, self.notebook.get_n_pages()):
            page = self.notebook.get_nth_page(i)
            # don't show the ATC page if we don't have an ATC.  Likewise with scanner
            if (i == ATC_PAGE):
                if self.atc.operational:
                    page.show()
                else:
                    page.hide()
            elif i == INJECTOR_PAGE:
                if self.injector_enabled == True:
                    page.show()
                else:
                    page.hide()
            elif i == CNC_SCANNER_PAGE:
                if self.scanner_enabled == True:
                    page.show()
                else:
                    page.hide()
            else:
                page.show()

    def refresh_touch_z_led(self):
        # set touch z button LED if the current tool has a non-zero offset
        # only if the touch_z button doesn't have focus
        if self.button_list['touch_z'].has_focus(): return
        if self.status.tool_offset[2] != 0:
            self.set_image('touch_z_image', 'touch_z_green_led.png')
        else:
            self.set_image('touch_z_image', 'touch_z_black_led.png')

    def refresh_atc_diagnostics(self):
        #self.atc.hey_hal(ATC_QUERY_SENSOR, ATC_ALL_SENSORS)
        # pressure sensor true means not enough pressure

        if self.hal["atc-pressure-status"]:
            self.set_image('pressure_sensor_led', 'LED-Yellow.png')
        else:
            self.set_image('pressure_sensor_led', 'LED-Black.png')

        # tray in - true means under spindle
        self.set_indicator_led('tray_in_led',self.hal["atc-tray-status"])

        # VFD true means spindle is running
        self.set_indicator_led('vfd_running_led',self.hal["atc-vfd-status"])

        pass

    def show_atc_diagnostics(self):
        self.image_list['tray_in_led'].show()
        self.image_list['vfd_running_led'].show()
        self.image_list['pressure_sensor_led'].show()
        self.builder.get_object('tray_in_text').show()
        self.builder.get_object('vfd_running_text').show()
        self.builder.get_object('pressure_sensor_text').show()

        pass

    def hide_atc_diagnostics(self):
        self.image_list['tray_in_led'].hide()
        self.image_list['vfd_running_led'].hide()
        self.image_list['pressure_sensor_led'].hide()
        self.builder.get_object('tray_in_text').hide()
        self.builder.get_object('vfd_running_text').hide()
        self.builder.get_object('pressure_sensor_text').hide()


    def update_tlo_label(self):
        # if the offset in the tool table doesn't match the one that's applied, then set the led
        # to red
        current_tool_offset = round(self.status.tool_table[self.status.tool_in_spindle].zoffset, 4)
        currently_applied_offset = round(self.status.tool_offset[2], 4)
        if (current_tool_offset != currently_applied_offset):
            # ignore while the ATC is changing tools or if it only happens once
            #if self.atc.in_a_thread.isSet() or self.hal["atc-ngc-running"]:
            if not self.atc.is_changing():
                self.tlo_mismatch_count += 1   # must exist fot 2 cycles to flag red
                if self.tlo_mismatch_count > 1 :
                    self.tlo_mismatch_count = 1 # lets not ever overflow
                    self.tlo_label.set_markup('<span foreground="yellow" background="red">%s</span>' % self.dro_long_format % (currently_applied_offset * self.get_linear_scale()))
        else:
            self.tlo_mismatch_count = 0    #it agrees - set white
            self.tlo_label.set_markup('<span foreground="white">%s</span>' % self.dro_long_format % (currently_applied_offset * self.get_linear_scale()))


        #else:
            #self.tlo_label.set_markup('<span foreground="white">0.000</span>' )




    def set_button_permissions(self):
        # the whole list is initialized to PERMISSION_OK_WHEN_NOT_ESTOPPED, and then buttons
        # with special priviledges are set here.

        # program control buttons
        self.button_list['cycle_start'].permission_level = PERMISSION_OK_WHEN_RUNNING_PROGRAM
        self.button_list['single_block'].permission_level = PERMISSION_OK_WHEN_RUNNING_PROGRAM
        self.button_list['m01_break'].permission_level = PERMISSION_OK_WHEN_RUNNING_PROGRAM
        self.button_list['feedhold'].permission_level = PERMISSION_OK_WHEN_RUNNING_PROGRAM
        self.button_list['stop'].permission_level = PERMISSION_ALWAYS
        self.button_list['coolant'].permission_level = PERMISSION_OK_WHEN_RUNNING_PROGRAM
        self.button_list['reset'].permission_level = PERMISSION_ALWAYS
        self.button_list['feedrate_override'].permission_level = PERMISSION_OK_WHEN_RUNNING_PROGRAM
        self.button_list['rpm_override'].permission_level = PERMISSION_OK_WHEN_RUNNING_PROGRAM
        self.button_list['maxvel_override'].permission_level = PERMISSION_OK_WHEN_RUNNING_PROGRAM
        self.button_list['edit_gcode'].permission_level = PERMISSION_OK_WHEN_IDLE
        self.button_list['spindle_range'].permission_level = PERMISSION_OK_WHEN_RUNNING_PROGRAM

        # ref buttons
        self.button_list['ref_x'].permission_level = PERMISSION_OK_WHEN_HOMING
        self.button_list['ref_y'].permission_level = PERMISSION_OK_WHEN_HOMING
        self.button_list['ref_z'].permission_level = PERMISSION_OK_WHEN_HOMING
        self.button_list['ref_a'].permission_level = PERMISSION_OK_WHEN_HOMING

        # update and clear errors buttons
        self.button_list['update'].permission_level = PERMISSION_ALWAYS
        self.button_list['clear'].permission_level = PERMISSION_ALWAYS
        self.button_list['switch_to_lathe'].permission_level = PERMISSION_ALWAYS

        # by popular demand of beta program, use conv. screens
        self.button_list['post_to_file'].permission_level = PERMISSION_ALWAYS
        self.button_list['append_to_file'].permission_level = PERMISSION_ALWAYS

        # Allow scanner camera to be toggled
        self.button_list['scanner_camera_on_off'].permission_level = PERMISSION_ALWAYS

    # ----------------------------------------------------
    # load item named in self.image_list with file
    # used for most if not all gtk.Images
    # ----------------------------------------------------

    def set_image(self, image_name, file_name):
        # look for pixbuf with this filename's image in it
        try:
            if self.image_list[image_name].get_pixbuf == self.pixbuf_dict[file_name]:
                print "bug here - we attempted to load this image when we didn't need to "
                return
            self.image_list[image_name].set_from_pixbuf(self.pixbuf_dict[file_name])
        except KeyError:
            # not yet loaded, attempt to load it then add to pixbuf dictionary
            try:
                self.image_list[image_name].set_from_file(os.path.join(GLADE_DIR, file_name))
                self.pixbuf_dict[file_name] = self.image_list[image_name].get_pixbuf()
            except:
                e = sys.exc_info() [0]
                print 'failed to load image %s with file %s.  Error: %s' % (image_name, file_name, e)




    # helper function for issuing MDI commands
    def issue_mdi(self, mdi_command):
        if self.moving(): return
        if self.ensure_mode(linuxcnc.MODE_MDI):
            self.error_handler.write("issuing MDI command: " + mdi_command, ALARM_LEVEL_DEBUG)
            self.command.mdi(mdi_command)


    # debug only??
    def get_lcnc_mode_string(self, mode):
        tmp_str = 'unknown'
        if mode == linuxcnc.MODE_MANUAL:
            tmp_str = 'MODE_MANUAL'
        elif mode == linuxcnc.MODE_AUTO:
            tmp_str = 'MODE_AUTO'
        elif mode == linuxcnc.MODE_MDI:
            tmp_str = 'MODE_MDI'
        return tmp_str

    def get_lcnc_interp_string(self, state):
        tmp_str = 'unknown'
        if state == linuxcnc.INTERP_IDLE:
            tmp_str = 'INTERP_IDLE'
        elif state == linuxcnc.INTERP_READING:
            tmp_str = 'INTERP_READING'
        elif state == linuxcnc.INTERP_PAUSED:
            tmp_str = 'INTERP_PAUSED'
        elif state == linuxcnc.INTERP_WAITING:
            tmp_str = 'INTERP_WAITING'
        return tmp_str

    def get_lcnc_state_string(self, state):
        tmp_str = 'unknown'
        if state == linuxcnc.STATE_ESTOP:
            tmp_str = 'STATE_ESTOP'
        elif state == linuxcnc.STATE_ESTOP_RESET:
            tmp_str = 'STATE_ESTOP_RESET'
        elif state == linuxcnc.STATE_OFF:
            tmp_str = 'STATE_OFF'
        elif state == linuxcnc.STATE_ON:
            tmp_str = 'STATE_ON'
        return tmp_str

    def load_reset_image(self, image_color):
        # for 'white' load white image if not already loaded
        # for 'blink': if now 'red' load 'non-red' else load 'red'
        if image_color == 'white' and self.reset_image_color != 'white':
            # if not already green, make it green
            self.set_image('reset_image', 'Reset-White.jpg')
            self.reset_image_color = 'white'
        elif image_color == 'blink':
            # blink between red and non-red
            if self.reset_image_color == 'red':
                # load non-red
                self.set_image('reset_image', 'Reset-White.jpg')
                self.reset_image_color = 'non-red'
            else:
                # load red
                self.set_image('reset_image', 'Reset-Red.jpg')
                self.reset_image_color = 'red'


    # periodic updates to LEDs, DROs, more . . .
    def periodic_status(self):
        # 50 ms functions is always called
        self.status_periodic_50ms()
        # increment loop counter and call slow period function as needed
        self.periodic_loopcount += 1
        if self.periodic_loopcount >= 10:
            self.status_periodic_500ms()
            self.periodic_loopcount = 0
        return True

    def update_spindle_direction_display(self):
        # update spindle direction
        self.spindle_direction = self.status.spindle_direction
        if self.spindle_direction != self.prev_spindle_direction:
            self.prev_spindle_direction = self.spindle_direction
            if self.spindle_direction == -1:
                # CCW
                self.set_image('ccw_image', 'REV_Green.jpg')
                self.set_image('cw_image', 'FWD_Black.jpg')
            elif self.spindle_direction == 0:
                # Off
                self.set_image('ccw_image', 'REV_Black.jpg')
                self.set_image( 'cw_image',  'FWD_Black.jpg')
            elif self.spindle_direction == 1:
                # CW
                self.set_image('ccw_image', 'REV_Black.jpg')
                self.set_image('cw_image',  'FWD_Green.jpg')

    def update_jog_leds(self):
        """ Handle updating of jog axis LED's to match HAL state"""

        jog_enabled = [self.hal['jog-axis-%s-enabled' % l] for l in self.axes.letters]

        for n,l in enumerate(self.axes.jog_active_leds):
            # Check if our local state doesn't match the HAL state.
            if jog_enabled[n] != self.axes.jog_enabled_local[n]:
                # HAL has changed, need to update the indicator to match the
                # new state
                self.set_indicator_led(l,jog_enabled[n])

        #Store the HAL state in the axes class:
        self.axes.jog_enabled_local = jog_enabled


    def zero_height_gauge_show_or_hide(self):
        if self.hal['hg-present'] == False:
            # hide the height gauge zero button if visible and gauge not present
            if self.zero_height_gauge_visible:
                self.button_list['zero_height_gauge'].hide()
                self.zero_height_gauge_visible = False
        else:
            # show if present and the old style, but but not currently visible
            if not self.zero_height_gauge_visible and not self.hal['hg-has-zero-button']:
                self.button_list['zero_height_gauge'].show()
                self.zero_height_gauge_visible = True



    # called every 500 milliseconds to update various slower changing DROs and button images
    def status_periodic_500ms(self):
        self.current_notebook_page = self.get_current_notebook_page()

        # get machine state
        machine_executing_gcode = self.program_running()
        if machine_executing_gcode:
            machine_busy = True
        else:
            # moving under MDI, probing, ATC ops, jogging, etc
            machine_busy = self.moving()

        if self.hal['mesa-watchdog-has-bit']:
            # problem! the Mesa card watchdog has bitten
            # high priority warning
            if not self.mesa_watchdog_has_bit_seen:
                # set state to ESTOP
                self.mesa_watchdog_has_bit_seen = True
                self.command.state(linuxcnc.STATE_ESTOP)
                self.error_handler.write("Mesa interface card watchdog has bitten. Must press RESET.", ALARM_LEVEL_MEDIUM)

            # redis-based messaging from asynchrnonous threads - DO NOT USE THIS FACILITY FROM THE MAIN GUI THREAD!!!!!!

            # This is here to allow popups from threads, and NGC prompts - which run asynchronously with GUI thread.
            # Messages requiring user tool change confirmation during a part program
            # go to the gremlin message line.  During non-part program they get a pop-up.
            # Font spacing in Gremlin and in popups is very different, so are the reply instructions
            # Mesaage strings contain '*' for spaces, and '$$REPLY_TEXT$$' for requested actions
            # at prompt time these are subtstituted with the appropriate number of spaces and phrases
            # respectively.

        try:
            request = self.redis.lpop("TormachMessage")  #pop one off the queue
        except Exception as e:
            print "Error in TormachRequest", e

        if (request):
            self.hal['prompt-reply'] = 0      #set hal signal to waiting

            parsed_request = request.split(':')
            if "AnswerKey" in parsed_request[0]:   #break down "AnswerKey:key:message" structure
                self.notify_answer_key = parsed_request [1]
                message =  parsed_request[2]
            else:
                message = parsed_request[0]   #it's all just a message

            if self.program_running():
                if (message) :
                    message = message.replace('*',' ')
                    message = message.replace('$$REPLY_TEXT$$','Press cycle start')
                    self.set_message_line_text(message)
                if (self.notify_answer_key) and (message):
                    self.notify_at_cycle_start = True

                #user now presses cycle start, stop or cancel - see those callbacks for setting prompt channel hal
            else:
                message = message.replace('*', '    ')
                message = message.replace('$$REPLY_TEXT$$','Click    OK    to    continue')
                dialog = tormach_file_util.ok_cancel_popup(message)
                dialog.run()
                ok_cancel_response = dialog.response
                dialog.destroy()
                if ok_cancel_response == gtk.RESPONSE_OK:
                    self.redis.hset("TormachAnswers",self.notify_answer_key,"Y")
                    self.ensure_mode(linuxcnc.MODE_MDI)
                    self.hal['prompt-reply'] = 1        #set hal to OK - need this pin incase a MDI M6 line was issued
                else:
                    self.redis.hset("TormachAnswers",self.notify_answer_key,"!")
                    self.ensure_mode(linuxcnc.MODE_MDI)
                    self.hal['prompt-reply']= 2          #set hal to CANCEL - need this pin incase a MDI M6 line was issued


        # if the ATC does not come up while system is not in RESET  notify user and swtich to manual
        #print self.atc.operational ,self.hal['atc-device-status'],self.status.task_state == linuxcnc.STATE_ON
        if  self.atc.operational and self.hal['atc-device-status'] == False and self.status.task_state == linuxcnc.STATE_ON:
            self.atc_hardware_check_count = self.atc_hardware_check_count + 1   #lets not panic yet.
            if self.atc_hardware_check_count == 30 :         #give 15 full second to stay broken.Hal startup o recovery may need some time here
                self.error_handler.write('Check ATC USB cabling, or fuses. Switching mill to manual toolchange. Repair problem. To re-enable, Click ATC in Settings tab. Wait 2 seconds for button to light')

                #switch to manual
                self.atc.disable()                                      #now panic! we need human help to reconnect
                self.hide_atc_diagnostics()
                self.checkbutton_list['use_manual_toolchange_checkbutton'].set_active(True)

        else: self.atc_hardware_check_count = 0 #we're in the clear now

        #---------------------------------------------------------------------------------
        # When the atc board is not communicating with the draw bar - both vfd and drawbar
        #    hal pins assert
        #----------------------------------------------------------------------------------
        if self.atc.operational and self.status.task_state == linuxcnc.STATE_ON \
        and self.hal['atc-vfd-status'] and self.hal['atc-draw-status'] \
        and self.only_one_cable_warning == False:
            self.atc_cable_check_count = self.atc_cable_check_count + 1   #lets not panic yet.
            if self.atc_cable_check_count == 30 :  # it's been steadily broken for 15 seconds, ok to alert

                self.only_one_cable_warning == True
                self.error_handler.write('Check ATC to Draw Bar cabling, or fuses. Switching mill to manual toolchange. Repair problem. To re-enable, Click ATC in Settings tab. Wait 2 seconds for button to light')

                #switch to manual - user can fix this and try again.
                self.atc.disable()                                      #now panic! we need human help to reconnect
                self.hide_atc_diagnostics()
                self.checkbutton_list['use_manual_toolchange_checkbutton'].set_active(True)
            else:
                self.atc_cable_check_count = 0    # reset checker count - not broken anymore


        # active gcodes label
        active_codes = " ".join(self.active_gcodes())
        self.active_gcodes_label.set_text(active_codes)

        self.update_spindle_direction_display()
        # reset button
        if self.status.task_state == linuxcnc.STATE_ESTOP or \
           self.status.task_state == linuxcnc.STATE_ESTOP_RESET or \
           self.status.task_state == linuxcnc.STATE_OFF:
            # blink
            self.load_reset_image('blink')
        else:
            # not in ESTOP or RESET or OFF
            # load white image
            self.load_reset_image('white')

        if self.hal['machine-ok'] == False:
            # machine-ok is False
            if self.estop_alarm == False and self.display_estop_msg:
                # only do this once per press press of reset
                # and don't alarm at startup
                self.display_estop_msg = False
                self.error_handler.write(ESTOP_ERROR_MESSAGE, ALARM_LEVEL_MEDIUM)
                self.command.unhome(0)
                self.command.unhome(1)
                self.command.unhome(2)
            # set to true to prevent these messages from stacking up.
            # cleared in reset button handler
            self.estop_alarm = True
        else:
            # machine-ok is True
            # check limit switches X Y Z status
            for axis_index in range(0, 3):
                #'3' means both pos and neg hard limit active which is the case with only one switch per axis
                if self.status.limit[axis_index] == 3:
                    #print 'axis: %d, prev_state: %d, state: %d' % (axis_index, self.prev_status_limit[axis_index], self.status.limit[axis_index])
                    # active now
                    if self.prev_status_limit[axis_index] == 3 and self.display_limit_msg[axis_index]:
                        # do not do anything if homing in progress
                        if not self.status.axis[axis_index]['homing']:
                            # display correct limit switch active message
                            if   axis_index == 0:
                                if self.door_sw_enabled:
                                    error_msg = X_Y_LIMIT_ERROR_MESSAGE
                                else:
                                    error_msg = X_LIMIT_ERROR_MESSAGE
                            elif axis_index == 1:
                                if self.door_sw_enabled:
                                    error_msg = X_Y_LIMIT_ERROR_MESSAGE
                                else:
                                    error_msg = Y_LIMIT_ERROR_MESSAGE
                            elif axis_index == 2: error_msg = Z_LIMIT_ERROR_MESSAGE
                            else:                 error_msg = 'Unknown axis limit switch active'
                            self.error_handler.write(error_msg, ALARM_LEVEL_MEDIUM)
                            # only print message once
                            self.display_limit_msg[axis_index] = False
                    else:
                        # current and previous state are not the same
                        # save current state as previous and continue
                        self.prev_status_limit[axis_index] = self.status.limit[axis_index]
                else:
                    # limit not active so allow next active state to display message
                    self.display_limit_msg[axis_index] = True

        # tool DRO
        if not self.dro_list['tool_dro'].masked:
            display_tool = self.status.tool_in_spindle
            if display_tool == -1 : display_tool = 0
            self.dro_list['tool_dro'].set_text(self.dro_short_format % display_tool)

        # metric/imperial switch
        self.update_gui_unit_state()

        #coolant button LED

        if self.hal['coolant'] != self.coolant_status:
            self.coolant_status = self.hal['coolant']

        if (self.hal['mist'] != self.mist_status):
            self.mist_status = self.hal['mist']

        if self.mist_status or self.coolant_status:
            self.set_image('coolant_image', 'Coolant-Green_11.png')
        else:
            self.set_image('coolant_image', 'Coolant-Black_11.png')


        # update self.s_word
        if self.s_word != self.status.settings[2]:
            self.s_word = self.status.settings[2]
            if not ((self.hal['spindle-min-speed'] <= self.s_word <= self.hal['spindle-max-speed']) or self.s_word == 0.0):
                self.error_handler.write('Invalid S command of %d.  RPM must be between %d and %d in the current belt position.' % (self.s_word, self.hal['spindle-min-speed'], self.hal['spindle-max-speed']), ALARM_LEVEL_LOW)


        #TODO refactor similar to home switch code, vectorize
        if not machine_executing_gcode:
            self.refresh_gremlin_offsets()
            self.update_jog_leds()
            if self.notebook_locked:
                self.show_enabled_notebook_tabs()
                self.notebook_locked = False

            # spindle rpm dro
            if not self.dro_list['spindle_rpm_dro'].masked:
                if self.door_sw_enabled and self.door_sw_status and self.hal['spindle-on'] and (self.s_word > self.enc_open_door_max_rpm):
                    self.dro_list['spindle_rpm_dro'].set_text(self.dro_short_format % abs(self.hal['spindle-speed-out']))
                else:
                    self.dro_list['spindle_rpm_dro'].set_text(self.dro_short_format % abs(self.s_word))

            # feed per rev and per rpm
            if not self.dro_list['feed_per_min_dro'].masked:
                if self.moving():
                    feed_per_min = self.status.current_vel * 60 * self.get_linear_scale()
                    self.dro_list['feed_per_min_dro'].set_text(self.dro_medium_format % feed_per_min)
                else:
                    self.f_word = abs(self.status.settings[1])
                    self.dro_list['feed_per_min_dro'].set_text(self.dro_medium_format % abs(self.f_word))
            # display active g code on settings screen
            if self.notebook.get_current_page() == SETTINGS_PAGE:
                self.gcodes_display.highlight_active_codes(self.active_gcodes())

            self.load_cs_image('dark')
            if self.current_notebook_page == OFFSETS_PAGE and not machine_busy: # don't update while probing a tool length with ETS, or CPU usage goes way up
                self.refresh_touch_z_led()
                # don't refresh liststore when user is trying to click into it!!
                if self.window.get_focus() == None:
                    self.highlight_offsets_treeview_row()
                self.zero_height_gauge_show_or_hide()
                if self.work_probe_in_progress and \
                   self.status.interp_state == linuxcnc.INTERP_IDLE:
                    # Interp idle after work probe; assume completed
                    self.refresh_work_offset_liststore()
                    self.work_probe_in_progress = False

            elif self.current_notebook_page == ATC_PAGE and self.atc.operational: #update the tray, and update drawbar state LED
                self.atc.display_tray()
                if self.hal["atc-draw-status"]:
                    self.set_image('atc_drawbar_image', 'Drawbar-Up-Green.png')
                else:
                    self.set_image('atc_drawbar_image', 'Drawbar-Down-Green.png')
            elif self.current_notebook_page == PROBE_PAGE:
                self.update_probing_dros()

            elif self.current_notebook_page == MILL_STATUS_PAGE:
                if self.usbio_enabled: self.refresh_usbio_interface()
                if self.atc.operational: self.refresh_atc_diagnostics()

            # temp kludge - TODO: understand limit overrides.
            if not self.first_run:
                # limit switch overrides
                if (self.status.limit[0] == 3) or (self.status.limit[1] == 3) or (self.status.limit[2] == 3):
                    self.command.override_limits()
            if self.status.limit[0] == 3:
                # only unhome if axis is referenced
                if self.x_referenced and not self.status.axis[0]['homing']:
                    self.command.unhome(0)
                    if self.door_sw_enabled:
                        if self.y_referenced:
                            self.command.unhome(1)
            if self.status.limit[1] == 3:
                # only unhome if axis is referenced
                if self.y_referenced and not self.status.axis[1]['homing']:
                    self.command.unhome(1)
                    if self.door_sw_enabled:
                        if self.x_referenced:
                            self.command.unhome(0)
            if self.status.limit[2] == 3:
                # only unhome if axis is referenced
                if self.z_referenced and not self.status.axis[2]['homing']:
                    self.command.unhome(2)

            # axis ref'ed button LEDs
            self.x_referenced = self.status.homed[0]
            self.y_referenced = self.status.homed[1]
            self.z_referenced = self.status.homed[2]
            self.a_referenced = self.status.homed[3]
            if self.x_referenced != self.prev_x_referenced:
                self.prev_x_referenced = self.x_referenced
                if self.x_referenced:
                    self.set_image('ref_x_image', 'Ref_X_Green.png')
                else:
                    self.set_image('ref_x_image', 'Ref_X_Black.png')

            if self.y_referenced != self.prev_y_referenced:
                self.prev_y_referenced = self.y_referenced
                if self.y_referenced:
                    self.set_image('ref_y_image', 'Ref_Y_Green.png')
                else:
                    self.set_image('ref_y_image', 'Ref_Y_Black.png')

            if self.z_referenced != self.prev_z_referenced:
                self.prev_z_referenced = self.z_referenced
                if self.z_referenced:
                    self.set_image('ref_z_image', 'Ref_Z_Green.png')
                else:
                    self.set_image('ref_z_image', 'Ref_Z_Black.png')

            if self.a_referenced != self.prev_a_referenced:
                # a is not a limit sw, so we never want it to come unreffed on trigger.  Need to look into this.
                if self.a_referenced:
                    self.set_image('ref_a_image', 'Ref_A_Green.png')
                else:
                    self.set_image('ref_a_image', 'Ref_A_Black.png')



        else:
            # machine is running a g code prorgram
            # lock the notebook
            if not self.notebook_locked:
                self.hide_notebook_tabs()
                self.notebook_locked = True
            # if we're running a program, use S value from HAL spindle-speed-out and F value from status.current_vel
            self.rpm = int(self.hal["spindle-speed-out"])
            feed_per_min = self.status.current_vel * 60 * self.get_linear_scale()
            self.dro_list['spindle_rpm_dro'].set_text(self.dro_short_format % abs(self.rpm))
            self.dro_list['feed_per_min_dro'].set_text(self.dro_medium_format % feed_per_min)

            self.elapsed_time_label.set_text('%02d:%02d:%02d' % (self.hal['cycle-time-hours'], self.hal['cycle-time-minutes'], self.hal['cycle-time-seconds']))

            # CS button
            if self.single_block_active or self.feedhold_active.is_set() or self.m01_break_active:
                if (self.status.current_vel == 0) and (self.maxvel_override_adjustment.get_value() != 0):
                    self.load_cs_image('blink')
                else:
                    self.load_cs_image('green')
            else:
                self.load_cs_image('green')

        self.update_tlo_label()

        if machine_busy:
            if not self.dros_locked:
                self.dros_locked = True
                # lock out DROs
                for name, dro in self.dro_list.iteritems():
                    dro.set_can_focus(False)
        else:
            # if gcode file is loaded and has changed on disk since loading, reload it
            if self.current_gcode_file_path != '':
                self.check_for_gcode_program_reload()

            # check custom thread files for changes, reload if necessary
            self.thread_custom_file_reload_if_changed()

            if self.dros_locked:
                self.dros_locked = False
                # unlock DROs
                for name, dro in self.dro_list.iteritems():
                    dro.set_can_focus(True)
            # catch need to refresh tool treeview from 'move and set tool length' button
            if self.tool_liststore_stale > 0:
                self.tool_liststore_stale -= 1
                if self.tool_liststore_stale == 0:
                    self.refresh_tool_liststore()


        # debug info - observe mode/status changes
        # this is far from perfect: the mode can change and return during time elapsed between these checks
        if self.status.task_mode != self.prev_lcnc_task_mode:
            # state changed, print to console
            print 'LinuxCNC status.task_mode change was %s is now %s' % (self.get_lcnc_mode_string(self.prev_lcnc_task_mode), self.get_lcnc_mode_string(self.status.task_mode))
            self.prev_lcnc_task_mode = self.status.task_mode
            #print '  interp_state %s' % (self.get_lcnc_interp_string(self.status.interp_state))
        #if self.status.task_mode != linuxcnc.MODE_AUTO:
        #    # not manual or MDI mode
        if self.prev_lcnc_interp_state != self.status.interp_state:
            # interpreter state changed
            print 'LinuxCNC interp_state change was %s is now %s' % (self.get_lcnc_interp_string(self.prev_lcnc_interp_state), self.get_lcnc_interp_string(self.status.interp_state))
            self.prev_lcnc_interp_state = self.status.interp_state
            # kludge to rewind program after interp goes idle (usually when program is done at M30)
            if "IDLE" in self.get_lcnc_interp_string(self.status.interp_state) and not self.first_run:
                self.gcodelisting_mark_start_line(1)
                self.sourceview.scroll_to_mark(self.gcodelisting_start_mark, 0, True, 0, 0.5)
            # State changes may result from M01 and a following cycle
            # start; display/hide any image specified in a comment
            # following M01
            if self.status.interp_state == linuxcnc.INTERP_PAUSED:
                self.show_m1_image()
            elif self.status.interp_state != linuxcnc.INTERP_PAUSED:
                self.hide_m1_image()

        if self.prev_task_state != self.status.task_state:
            print "status.task_state was %s is now %s" % (self.get_lcnc_state_string(self.prev_task_state), self.get_lcnc_state_string(self.status.task_state))
            self.prev_task_state = self.status.task_state

        self.update_scanner_state()

        # log abnormal changes in cpu utilization
        usage = self.proc.cpu_percent()
        if usage > 15 and (usage > 2 * self.cpu_usage) or (usage < .5 * self.cpu_usage) or (usage > CPU_USAGE_THRESHOLD):
            self.error_handler.write("CPU usage was %.1f, is now %.1f" % (self.cpu_usage, usage), ALARM_LEVEL_DEBUG)
            self.cpu_usage = usage


    def update_scanner_state(self):
        if self.scanner is None:
            return
        status_label = self.get_obj('scanner_scan_status_label')
        if not self.scanner.status_queue.empty():
            s = self.scanner.status_queue.get()
            #logging.debug("At point {0}, completed {1}".format(s[0],s[1]))
            if len(s[0]):
                status_label.set_markup(self.format_dro_string('Points done: {0}'.format(s[1]),11))
            else:
                status_label.set_markup(self.format_dro_string('--',11))
        elif self.scanner.complete_event.is_set():
            status_label.set_markup(self.format_dro_string('Scan Complete',11))

    def update_gui_unit_state(self):
        is_metric = self.status.gcodes[5] == 210
        if self.g21 == is_metric:
            return

        self.g21 = is_metric

        # swap button art on jog step sizes
        self.clear_jog_LEDs()
        self.set_jog_LEDs()
        # store off in redis for startup in same mode next time.
        self.redis.hset('machine_prefs', 'g21', self.g21)
        if self.g21:
            self.dro_long_format = "%3.3f"
            self.jog_metric_scalar = 10
            self.hal['jog-is-metric'] = True
            self.gremlin.grid_size = (10.0/25.4)
            self.ttable_conv = 25.4
        else:
            self.dro_long_format = "%2.4f"
            self.jog_metric_scalar = 1
            self.hal['jog-is-metric'] = False
            self.gremlin.grid_size = 0.5
            self.ttable_conv = 1.0
        self.gremlin._redraw()

        # force refresh of Offsets tab lengths and diameters
        self.refresh_tool_liststore(True)

        #TODO update Scanner DRO's?

    def update_probing_dros(self):
        probing_current = self.status.probing
        # probe type is set by 'find_whatever' functions, 1 = find_x_plus, 2 = X-, 3 = Y+, 4 = Y-, 5 = ?
        self.probe_x_plus_label.set_markup('<span foreground="white">%s</span>' % self.dro_long_format % self.status.aout[11])
        self.probe_x_minus_label.set_markup('<span foreground="white">%s</span>' % self.dro_long_format % self.status.aout[12])
        self.probe_y_plus_label.set_markup('<span foreground="white">%s</span>' % self.dro_long_format % self.status.aout[13])
        self.probe_y_minus_label.set_markup('<span foreground="white">%s</span>' % self.dro_long_format % self.status.aout[14])
        self.probe_z_minus_label.set_markup('<span foreground="white">%s</span>' % self.dro_long_format % self.status.aout[15])
        self.probe_y_plus_a_label.set_markup('<span foreground="white">%s</span>' % self.dro_long_format % self.status.aout[16])
        self.probe_y_plus_b_label.set_markup('<span foreground="white">%s</span>' % self.dro_long_format % self.status.aout[17])
        self.probe_y_plus_c_label.set_markup('<span foreground="white">%s</span>' % self.dro_long_format % self.status.aout[18])
        if not self.dro_list['ets_height_dro'].masked:
            self.dro_list['ets_height_dro'].set_text(self.dro_long_format % (self.get_linear_scale() * self.ets_height))

    # Utility functions for position translation
    #FIXME doesn't handle axis rotation
    def to_local_position(self,global_position,axis = None):
        #FIXME needs well-formatted input
        if axis is None :
            return [self.get_axis_scale(ind) * (global_position[ind] - self.status.g5x_offset[ind] - self.status.tool_offset[ind] - self.status.g92_offset[ind]) for ind in range(4)]
        else:
            return self.get_axis_scale(axis) * (global_position - self.status.g5x_offset[axis] - self.status.tool_offset[axis] - self.status.g92_offset[axis])

    def to_global_position(self,local_position,axis=None):
        #FIXME needs well-formatted input
        if axis is None:
            return [(local_position[ind] + self.status.g5x_offset[ind] + self.status.tool_offset[ind] + self.status.g92_offset[ind] / self.get_axis_scale[ind]) for ind in range(4)]
        else:
            return (local_position + self.status.g5x_offset[axis] + self.status.tool_offset[axis] + self.status.g92_offset[axis] / self.get_axis_scale(axis))

    def get_local_position(self):
        if self.status.rotation_xy == 0:
            return [self.get_axis_scale(ind) * (self.status.actual_position[ind] - self.status.g5x_offset[ind] - self.status.tool_offset[ind] - self.status.g92_offset[ind]) for ind in range(4)]
        else:
            x = self.status.actual_position[0] - self.status.g5x_offset[0] - self.status.tool_offset[0]
            y = self.status.actual_position[1] - self.status.g5x_offset[1] - self.status.tool_offset[1]
            t = math.radians(-self.status.rotation_xy)
            xr = x * math.cos(t) - y * math.sin(t)
            yr = x * math.sin(t) + y * math.cos(t)
            # G92 offsets are not rotated - the apply post-rotation (should check with Smid)
            x = xr - self.status.g92_offset[0]
            y = yr - self.status.g92_offset[1]
            z = self.get_axis_scale(2) * (self.status.actual_position[2] - self.status.g5x_offset[2] - self.status.tool_offset[2] - self.status.g92_offset[2])
            a = self.get_axis_scale(3) * (self.status.actual_position[3] - self.status.g5x_offset[3] - self.status.tool_offset[3] - self.status.g92_offset[3])
            return [x, y, z, a]

    def refresh_gremlin_offsets(self):
        if self.current_g5x_offset != self.status.g5x_offset:
            self.current_g5x_offset = self.status.g5x_offset
            self.redraw_gremlin()
        elif self.current_g92_offset != self.status.g92_offset:
            self.current_g92_offset = self.status.g92_offset
            self.redraw_gremlin()

    def redraw_gremlin(self):
        # redraw screen with new offset
        # be sure to switch modes to cause an interp synch, which
        # writes out the var file.
        self.ensure_mode(linuxcnc.MODE_MANUAL)
        self.ensure_mode(linuxcnc.MODE_MDI)
        self.gremlin.clear_live_plotter()
        self.gremlin.load()
        #Note:not catching warnings here since it's assumed the user has
        #already seen them



    def get_machine_bounding_box(self):
        """ Crude function to poll axis limits"""
        min_bounds=[self.status.axis[ind]['min_position_limit'] for ind in range(4)]
        max_bounds=[self.status.axis[ind]['max_position_limit'] for ind in range(4)]
        return np.array(min_bounds), np.array(max_bounds)

    def check_limits(self,abs_position,axis):
        min_bound=self.status.axis[axis]['min_position_limit']
        max_bound=self.status.axis[axis]['max_position_limit']

        if abs_position < min_bound or abs_position > max_bound:
            return False
        else:
            return True

    def validate_local_position(self,local_position,axis):
        abs_pos = self.to_global_position(local_position,axis)
        if not self.check_limits(abs_pos,axis):
            err_msg = 'Position {0} on axis {1} is outside of machine limits!'.format(local_position,axis)
            return False,err_msg
        return True, ''

    def get_probe_tripped_position(self):
        return [self.get_axis_scale(ind) * (self.status.probed_position[ind] - self.status.g5x_offset[ind] - self.status.tool_offset[ind] - self.status.g92_offset[ind]) for ind in range(3)]

    def scanner_periodic(self):

        tab_title = None
        if (self.current_notebook_page == CNC_SCANNER_PAGE) and self.scanner:

            #Taken from kirk's code
            active_camera_child = self.camera_notebook.get_nth_page(self.camera_notebook.get_current_page())
            tab_title = self.camera_notebook.get_tab_label_text(active_camera_child)

        if self.scanner:
            glib.idle_add(self.scanner.periodic_update, tab_title)
        return True

    def usb_IO_periodic (self):
        # users who depend on the IO board could have critical requirements. If USB is enabled, all
        # boards connected to the system must be up and running.
        # all boards are enumerated enmasse when radio button is enabled.
        if self.hal['usbio-status'] == 0 :
            self.usbio_e_message = True      #okay to print messages if going bad
        if self.hal['usbio-status'] < 0 and self.usbio_enabled and self.program_running():
            if self.usbio_e_message == True :  #we transitioned to bad from good
                self.usbio_e_message = False   #don't print until we are good again
                if self.hal['usbio-status'] == -1:
                    self.error_handler.write('USBIO : Board malfunction. Cannot connect to board.')
                if self.hal['usbio-status'] == -2:
                    self.error_handler.write('USBIO : Board malfunction. Unrecoverable IO error.')
                if self.hal['usbio-status'] == -3:
                    self.error_handler.write('USBIO : Board malfunction. Duplicate board IDs. ')
                if self.hal['usbio-status'] == -4:
                    self.error_handler.write('USBIO : Board malfunction. All boards not commnicating. ')

            '''
            self.redis.hset('machine_prefs', 'usbio_enabled', 'False')
            self.usbio_enabled = False
            self.checkbutton_list['enable_usbio_checkbutton'].set_active(False)
            '''
            self.stop_motion_safely()         #end this show



    def coolant_periodic(self):
        # Coolant: watch for LinuxCNC to pulse coolant pin.
        # when it does copy finalstate tormach.coolant HAL pin. It will be
        # pulsed for .1 second by linuxcnc , so we debounce and wait for it
        # to settle to avoid spurious state changes

        self.coolant_ticker += 1   #tick it up
        self.mist_ticker += 1

        if not self.hardkill_coolant:

            if (self.prev_coolant_iocontrol != self.hal["coolant-iocontrol"]) :
                self.coolant_apply_at = self.coolant_ticker + 4  #schedule after pulse settles


            if  self.coolant_ticker == self.coolant_apply_at :
                self.hal['coolant'] = self.hal["coolant-iocontrol"]
                self.coolant_ticker = self.coolant_apply_at = 0           #new game

            if (self.prev_mist_iocontrol != self.hal["mist-iocontrol"]) :
                self.mist_apply_at = self.mist_ticker + 4  #schedule after pulse settles


            if  self.mist_ticker == self.mist_apply_at :
                self.hal['mist'] = self.hal["mist-iocontrol"]
                self.mist_ticker = self.mist_apply_at = 0

        if self.hardkill_coolant:

            self.hal['mist'] = self.hal['coolant'] = False
            if self.coolant_ticker > 20:
                self.coolant_ticker = 0
                self.hardkill_coolant = False

        # current becomes previous
        self.prev_coolant_iocontrol = self.hal["coolant-iocontrol"]
        self.prev_mist_iocontrol = self.hal["mist-iocontrol"]



    # called every 50 milliseconds to update faster changing indicators
    def status_periodic_50ms(self):
        # check button events from keyboard shortcuts
        self.check_keyboard_shortcut_fifo()

        # get new info
        self.status.poll()

        # The following updates are always performed, regardless of machine state

        # Position DROs and DTG labels:
        pos_scaled = self.get_local_position()

        # Get scaled distance to go for all axes
        dtg_scaled = [self.status.dtg[ind] * self.get_axis_scale(ind) for ind in range(4)]

        #For each axis in the DRO list, check if it's masked and update the position if need be
        for n,dro in enumerate(self.axes.dros):
            if not self.dro_list[dro].masked:
                self.dro_list[dro].set_text(self.dro_long_format % pos_scaled[n])
            #Regardless, update the DTG value
            dtg_label = self.get_obj(self.axes.dtg_labels[n])
            dtg_label.set_text(self.dro_long_format % dtg_scaled[n] )


        self.coolant_periodic ()
        self.usb_IO_periodic ()


        # door switch status
        self.door_sw_status = self.hal['enc-door-switch-status']
        if self.door_sw_status != self.prev_door_sw_status:
            self.prev_door_sw_status = self.door_sw_status
            if self.door_sw_status and self.program_running(False):
                # pause program
                self.error_handler.write("Pausing program because door sw was opened", ALARM_LEVEL_DEBUG)
                self.program_paused_for_door_sw_open = True
                self.command.auto(linuxcnc.AUTO_PAUSE)
                self.feedhold_active.set()
                self.set_image('feedhold_image', 'Feedhold-Green.jpg')
                if self.hal['coolant']:
                    self.hal['coolant'] = False

        # poll for errors
        error = self.error.poll()
        if error:
            error_kind, error_msg = error
            if error_kind == EMC_OPERATOR_DISPLAY_TYPE:
                # maybe revisit this after discussion - dispaly on gremlin message line?
                #self.set_message_line_text(error_msg)
                self.error_handler.write(error_msg, ALARM_LEVEL_LOW)
            else:
                # display on UI
                self.error_handler.write(error_msg)
                if self.atc.in_a_thread.isSet() :
                    self.atc.general_error.set()   #abort the ATC unit of work due to errors here

        # the following updates are only performed if we ARE running a g code program
        self.update_gcode_display()

        self.update_jogging()

        # the following updates are performed only if the current page requires it
        if self.current_notebook_page == OFFSETS_PAGE:
            self.update_mill_acc_input_leds()
            # height gauge update upon button press
            if self.hal['hg-button-changed'] and self.hal['hg-button-pressed']:
                self.hal['hg-button-changed'] = False
                self.on_height_gauge_button_press_event()

        elif self.current_notebook_page == MILL_STATUS_PAGE:
            self.update_mill_status_leds()
        elif self.current_notebook_page == PROBE_PAGE or self.current_notebook_page == INJECTOR_PAGE or self.current_notebook_page == ATC_PAGE:
            self.update_mill_acc_input_leds()

    def handle_step_jog(self):
        """Inner wheel step jogging"""
        jog_step_counts = self.hal['jog-counts']
        # if in a continuous jog do not do a step jog
        if self.jogging_stopped == False and jog_step_counts != self.prev_hal_jog_counts:
            count_delta = jog_step_counts - self.prev_hal_jog_counts

            # Choose jogging direction
            jog_dir = -1.0 if count_delta < 0 else 1.0

            if self.set_jog_mode(linuxcnc.JOG_INCREMENT):
                # set UI LEDs to indicate step jog distance
                self.clear_jog_LEDs()
                self.set_jog_LEDs()
                self.jog(self.jog_ring_axis, jog_dir, self.jog_speed,False)

    def handle_ring_jog(self):
        """Jog ring handling"""
        ring_speed = self.hal['jog-ring-speed-signed']
        self.jog_ring_axis = self.hal['jog-ring-selected-axis']
        jog_ring_axis_changed = False
        if self.jog_ring_axis != self.prev_jog_ring_axis:
            # NB - must ensure mode here, as it can't be handled in the stop_jog method for race condition reasons (see issue 827)
            self.ensure_mode(linuxcnc.MODE_MANUAL)
            self.stop_jog(self.prev_jog_ring_axis)
            self.prev_jog_ring_axis = self.jog_ring_axis
            jog_ring_axis_changed = True

        if self.jog_ring_axis >= 0 and (ring_speed != self.prev_jog_ring_speed or jog_ring_axis_changed):
            self.prev_jog_ring_speed = ring_speed

            jog_dir = -1.0 if ring_speed < 0.0 else 1.0

            # need new jog command
            # FIXME account for jog axis minimum speed here?
            if ring_speed == 0:
                self.stop_jog(self.jog_ring_axis)
            else:
                #Pass in extra argument to override stock jog mode
                self.set_jog_mode(linuxcnc.JOG_CONTINUOUS)
                self.jog(self.jog_ring_axis, jog_dir, abs(ring_speed), False, jog_mode = linuxcnc.JOG_CONTINUOUS)

    def handle_step_button(self):
        """step button - upon release advance or wrap to the next increment"""
        if self.hal['jog-step-button'] == 1:
            self.jog_step_button_was_pressed = 1
        elif self.hal['jog-step-button'] == 0 and self.jog_step_button_was_pressed:
            self.jog_step_button_was_pressed = 0
            if not self.set_jog_mode(linuxcnc.JOG_INCREMENT):
                #failed to change to step mode, so we can't update the increment
                return
            #beep()
            self.jog_increment = self.jog_increment * 10
            # wrap if needed
            if self.jog_increment > 0.1:
                self.jog_increment = 0.0001
            self.clear_jog_LEDs()
            self.set_jog_LEDs()


    def update_jogging(self):
        """During fast update loop, handle jogging keypresses"""
        if self.program_running():
            #Track jog counts
            self.prev_hal_jog_counts = self.hal['jog-counts']
            #Can't jog, we're done here
            return

        # Shuttle
        # force mode switch - needs MODE_MANUAL for jogging to function
        if self.hal['jog-axis-x-enabled'] or self.hal['jog-axis-y-enabled'] or self.hal['jog-axis-z-enabled'] or self.hal['jog-axis-a-enabled']:
            if (self.hal['jog-counts'] != self.prev_hal_jog_counts) or (self.hal['jog-ring-speed-signed'] != 0.0):
                self.ensure_mode(linuxcnc.MODE_MANUAL)

        self.handle_step_jog()

        self.handle_ring_jog()

        self.handle_step_button()

        # always reset previous jog counts
        self.prev_hal_jog_counts = self.hal['jog-counts']

    def update_mill_acc_input_leds(self):
        # diagnostic LEDs
        # probe input
        if bool(self.status.probe_val) != self.probe_tripped_display:
            self.probe_tripped_display = bool(self.status.probe_val)
            self.set_indicator_led('acc_input_led1',self.probe_tripped_display)
            self.set_indicator_led('acc_input_led2',self.probe_tripped_display)
            self.set_indicator_led('acc_input_led3',self.probe_tripped_display)
            if self.probe_tripped_display:
                self.set_image('ets_image', 'Sensor-set-LED.png')
                self.set_image('touch_entire_tray_ets_image', 'Sensor-set-LED.png')
                self.set_image('probe_sensor_set_image', 'Sensor-set-LED.png')
                self.set_image('injection_molder_image', 'Injection Molder Lit LED.png')
            else:
                self.set_image('ets_image', 'Sensor-set-No-LED.png')
                self.set_image('touch_entire_tray_ets_image', 'Sensor-set-No-LED.png')
                self.set_image('probe_sensor_set_image', 'Sensor-set-No-LED.png')
                self.set_image('injection_molder_image', 'Injection Molder.png')



    def update_mill_status_leds(self):
        # diagnostic LEDs
        # probe input
        if bool(self.status.probe_val) != self.probe_tripped_display:
            self.probe_tripped_display = bool(self.status.probe_val)
            self.set_indicator_led('acc_input_led',self.probe_tripped_display)

        # machine ok LED
        if bool(self.hal['machine-ok']) != self.machine_ok_display:
            self.machine_ok_display = bool(self.hal['machine-ok'])
            self.set_indicator_led('machine_ok_led',self.machine_ok_display)

        # door sw LED
        if self.door_sw_enabled:
            self.set_indicator_led('door_sw_led', self.door_sw_status)
        else:
            self.set_indicator_led('door_sw_led', False)

        # limit switch virtual LED updates
        for n,sw in enumerate(self.axes.home_switches):
            if self.door_sw_enabled and (n == 0):
                # leave X axis switch off
                self.set_indicator_led(self.axes.limit_leds[n], False)
                continue
            # Change button state only on change of state
            if bool(self.hal[sw]) != self.axes.at_limit_display[n]:
                self.axes.at_limit_display[n] = self.hal[sw]
                self.set_indicator_led(self.axes.limit_leds[n],self.hal[sw])


    def on_entry_loses_focus(self, widget, data=None):
        # get rid of text highlight if you click out of a dro that has highlighted text
        widget.select_region(0, 0)
        return False

    def set_work_offset(self, axis, dro_text):
        try:
            dro_val = float(dro_text)
        except:
            print "%s DRO entry is not a number '%s'" % (axis, dro_text)
            return
        current_work_offset = self.status.g5x_index
        offset_command = "G10 L20 P%d %s%.12f" % (current_work_offset, axis, dro_val)
        self.issue_mdi(offset_command)


    def check_button_permissions(self, widget):
        # move the button back, ditch focus.
        do_button_release_motion(widget)
        self.window.set_focus(None)

        # get required permission level, which is an integer between 1 and 5, with 1 requiring the highest
        # level of permission (e.g. reset button always works) and 5 requiring the least (can't press it
        # unless the machine is idle)
        if self.program_running():
            # we're running a g code program
            required_permission_level = PERMISSION_OK_WHEN_RUNNING_PROGRAM
        elif self.moving():
            # machine is moving (e.g. jog, MDI) or atc is doing something
            required_permission_level = PERMISSION_OK_WHEN_MOVING
            if self.status.axis[0]['homing'] or self.status.axis[1]['homing'] or self.status.axis[2]['homing']:
                required_permission_level = PERMISSION_OK_WHEN_HOMING
        elif self.status.task_state == linuxcnc.STATE_ON:
            # machine is on, connected, not moving or running g code
            required_permission_level = PERMISSION_OK_WHEN_IDLE
        else:
            # machine is in ESTOP state
            required_permission_level = PERMISSION_ALWAYS
        return widget.permission_level <= required_permission_level


    def program_running(self, do_poll=False):
        # are we executing a g code program?
        if do_poll:
            # need fresh status data, ask for it
            self.status.poll()
        return self.status.task_mode == linuxcnc.MODE_AUTO and self.status.interp_state != linuxcnc.INTERP_IDLE

    """ Check if we are moving or running a motion command in coordinated mode.
    Can be used to check if feedhold should be allowed.
    """
    def command_in_progress(self, do_poll=False):
        if do_poll:
            # need fresh status data, ask for it
            self.status.poll()
        return self.status.interp_state != linuxcnc.INTERP_IDLE or self.status.queue > 0 or self.status.paused

    def ensure_mode(self, mode):
        if self.status.task_mode == mode:
            # if already in desired mode do nothing
            return True
        if self.moving():
            # if running a program do nothing
            return False
        # set the desired mode
        print "ensure_mode: changing LCNC mode to %s" % (self.get_lcnc_mode_string(mode))
        self.command.mode(mode)
        self.command.wait_complete()
        return True

    def active_gcodes(self):
        desired_codes = [8,6,5,1,4,7,13,10]
        active_codes = []
        for i in desired_codes:
            code = self.status.gcodes[i]
            if code % 10 == 0:
                active_codes.append("G%d" % (code/10))
            else:
                active_codes.append("G%(ones)d.%(tenths)d" % {'ones': code/10, 'tenths': code%10})
        return active_codes

    def on_height_gauge_button_press_event(self):
        try:
            store, tree_iter = self.treeselection.get_selected()
            # if no row is selected, the iter returned is "None" and the set will fail
            if tree_iter == None: return
            tool_number = store.get_value(tree_iter, 0)
            tool_length = self.hal['hg-height'] * self.get_linear_scale()
            self.issue_tool_offset_command('Z', tool_number, tool_length)
            store.set(tree_iter, 3, (self.dro_long_format % tool_length))
            if tool_number == self.status.tool_in_spindle:
                # apply offset right away if we are measuring the current tool
                self.issue_mdi('G43')
            # do not move to the next line - it is a source or overwriting
            # the next tool via mulitple presses of the button the USB gauge
        except:
            #FIXME don't do global exception handling
            self.error_handler.write("Height gauge error", ALARM_LEVEL_DEBUG)



    def refresh_tool_liststore(self, force=False):
        linear_scale = self.get_linear_scale()

        self.tool_liststore.clear()
        max_tools = MAX_NUM_MILL_TOOL_NUM
        for pocket in range(1, max_tools + 1):
            tool_num = self.status.tool_table[pocket].id
            try:
                description = self.redis.hget('tool_descriptions', str(tool_num))
            except:
                description = "None"
            diameter = self.dro_long_format % (self.status.tool_table[pocket].diameter * linear_scale)
            length = self.dro_long_format % (self.status.tool_table[pocket].zoffset * linear_scale)
            self.tool_liststore.append([tool_num, description, diameter, length])


    def g5x_offset_gcode_from_ix(self,offset_ix):
        return ("G%d" % (offset_ix + 54)) if offset_ix <= 5 \
            else ("G59.%d" % (offset_ix -5))

    def refresh_work_offset_liststore(self):
        # Init:  save current offset index; MDI mode; clear offset table
        self.status.poll()
        current_offset_ix = self.status.g5x_index - 1
        self.command.mode(linuxcnc.MODE_MDI)
        self.work_liststore.clear()
        # Switch to each work offset G54-G59.3 and read offsets
        for offset_ix in range(9):
            offset_gcode = self.g5x_offset_gcode_from_ix(offset_ix)
            self.command.mdi(offset_gcode)
            self.command.wait_complete()
            self.status.poll()
            self.work_liststore.append(
                [offset_gcode] +
                ['%.4f' % (i * self.get_linear_scale())
                 for i in self.status.g5x_offset[:4]] +

                ['GREY', 'WHITE'])
        # Restore current offset index
        self.command.mdi(self.g5x_offset_gcode_from_ix(current_offset_ix))
        self.command.wait_complete()
        # highlight active work offset
        row = self.work_liststore[current_offset_ix]
        row[5] = BLACK
        row[6] = ROW_HIGHLIGHT




    def load_cs_image(self, color):
        if color == 'green' and self.cycle_start_led_color != 'green':
            self.set_image('cycle_start_image', 'Cycle-Start-Green.jpg')
            self.cycle_start_led_color = 'green'
            return
        if color == 'dark' and self.cycle_start_led_color != 'dark':
            self.set_image('cycle_start_image', 'Cycle-Start-Black.jpg')
            self.cycle_start_led_color = 'dark'
            return
        if color == 'blink':
            if self.cycle_start_led_color == 'green':
                self.set_image('cycle_start_image', 'Cycle-Start-Black.jpg')
                self.cycle_start_led_color = 'dark'
                return
            else:
                self.set_image('cycle_start_image', 'Cycle-Start-Green.jpg')
                self.cycle_start_led_color = 'green'
                return



    def get_ttfont_name(self, font_file_name):
        #from fontTools import ttLib

        FONT_SPECIFIER_NAME_ID = 4
        FONT_SPECIFIER_FAMILY_ID = 1

        name = ""
        family = ""

        if is_ttlib == True:
            try:
                font = ttLib.TTFont(font_file_name)
            except:
                #print "--kw no font name found", font_file_name
                return name, family
        else:
            self.error_handler.write('ttLib module not loaded. Is fontTools installed?', ALARM_LEVEL_LOW)
            return name, family

        """Get the short name from the font's names table"""
        for record in font['name'].names:
            if record.nameID == FONT_SPECIFIER_NAME_ID and not name:
                if '\000' in record.string:
                    name = unicode(record.string, 'utf-16-be').encode('utf-8')
                else:
                    name = record.string
            elif record.nameID == FONT_SPECIFIER_FAMILY_ID and not family:
                if '\000' in record.string:
                    family = unicode(record.string, 'utf-16-be').encode('utf-8')
                else:
                    family = record.string
            if name and family:
                break
        return name, family

    def set_response_cancel (self) :

        if self.notify_at_cycle_start:  # is anyone waiting on us
            self.notify_at_cycle_start = False
            try:
                self.redis.hset("TormachAnswers",self.notify_answer_key,"!")  #start pressed message
                self.hal['prompt-reply'] = 2
                print ('prompt output pin set to 2 by cancel/reset')
            except Exception as e:
                print "Whooops! - Tormach message reply not set", e

        self.hal['atc-ngc-running'] = False       # cancel any NGC running conditions.

        if self.atc.in_a_thread.isSet() :
            self.atc.stop_reset.set()   #only if atc thread in progress
        if self.atc.feed_hold.isSet() :
            self.atc.feed_hold.clear()  # if it's set , clear it now

            return True
        return False

    @staticmethod
    def format_dro_string(input_string, fontsize):
        #TODO implement word spacing
        spaced_string = re.sub(' ','    ',input_string)
        spaced_string = re.sub(':','    :',spaced_string)
        return '<span weight="light" font_desc="Bebas {0}" font_stretch="ultracondensed" foreground="white" >{1}</span>'.format(fontsize, spaced_string)


    def delete_event(self, widget, event):
        print 'Alt-F4/delete_event detected. Simulating Exit button press.'
        try:
            self.enqueue_button_press_release(self.button_list['exit'])
        except Exception as e:
            print 'enqueue button press failed'
            msg = "An exception of type {0} occured, these were the arguments:\n{1!r}"
            print msg.format(type(e).__name__, e.args)
        return True

    def ja_gremlin(self, width, height):
        return jaGremlin(self,width,height)


#--end 'mill'-------------------------------------------------------------------



def is_dro_masked(dro_list):
    for name, dro in dro_list.iteritems():
        if dro.masked == True:
            return True
    return False

def beep():
    try:
        os.system("beep -f 440 -l 40")
    except:
        pass


class Tormach_Mill_Gremlin(gremlin.Gremlin):
    def __init__(self, ui, width, height):
        gremlin.Gremlin.__init__(self, ui.inifile)
        self.status = ui.status
        self.ui_view = 'p'
        self.ui = ui
        self.g21 = self.status.gcodes[5] == 210
        self.grid_size = (10.0/25.4) if self.g21 else 0.5
        self.ui=ui
        self.connect("button_press_event", self.on_gremlin_double_click)
        self.set_size_request(width, height)

    def realize(self,widget):
        super(Tormach_Mill_Gremlin, self).realize(widget)

    def set_grid_size(self, size):
        self.grid_size = size
        self._redraw()

    # necessary to support recent changes to gremlin in 2.6.  We might want to make this configurable
    # down the road, but for now it's set to a grid of .1 inches.  The grid doesn't display for me
    # but at least the ui will load without error again.
    ###def get_grid_size(self):
    ###    return .5

    def get_view(self):
        # gremlin as used as a gladevcp widegt has a propery for the view, which for a lathe
        # should be 'y'.  When it's not right the program extents won't be drawn.
        view_dict = {'x':0, 'y':1, 'z':2, 'p':3}
        return view_dict.get(self.ui_view)

    def get_show_metric(self):
        if self.status.gcodes[5] == 200:
            return False
        else:
            return True

    def posstrs(self):
        l, h, p, d = gremlin.Gremlin.posstrs(self)
        return l, h, [''], ['']

    def report_gcode_error(self, result, seq, filename):
        import gcode
        error_str = gcode.strerror(result)
        error_str = "\n\nG-Code error in " + os.path.basename(filename) + "\n" + "Near line: " + str(seq) + "\n" + error_str + "\n"
        self.ui.error_handler.write(error_str)
        self.ui.interp_alarm = True

    def report_gcode_warnings(self, warnings, filename, suppress_after = 3):
        """ Show the warnings from a loaded G code file.
        Accepts a list of warnings produced by the load_preview function, the
        current filename, and an optional threshold to suppress warnings after.
        """

        num_warnings = len(warnings)
        if num_warnings == 0:
            return

        # Find the maximum number of warnings to print
        max_ind = min(max(suppress_after,0), num_warnings)
        # Find out how many we're suppressing if any
        num_suppressed = max(num_warnings-max_ind,0)

        # warn, but still switch to main page if loading the file
        self.ui.notebook.set_current_page(MAIN_PAGE)

        #Iterate in reverse to print a coherent list to the status window, which shows most recent first
        if num_suppressed:
            self.ui.error_handler.write("Suppressed %d more warnings" % num_suppressed, ALARM_LEVEL_LOW)
        else:
            if num_warnings > 1: self.ui.error_handler.write("*** End of warning list ***", ALARM_LEVEL_LOW)
        for w in warnings[max_ind::-1]:
            # Add a space to show that the warning is part of the list
            self.ui.error_handler.write("  "+w, ALARM_LEVEL_LOW)

        warning_header = "G-Code warnings in %s " % os.path.basename(filename) + ":"
        self.ui.error_handler.write(warning_header, ALARM_LEVEL_LOW)

        self.ui.interp_alarm = True

    def on_gremlin_double_click(self, widget, event, data=None):
        if event.type == gtk.gdk._2BUTTON_PRESS:
            self.clear_live_plotter()
            return
        if event.type == gtk.gdk.BUTTON_PRESS and event.button == 3:
            # it's a right click if event.button == 3
            menu = gtk.Menu()
            set_front_view = gtk.MenuItem("Front View")
            set_top_view = gtk.MenuItem("Top View")
            set_side_view = gtk.MenuItem("Side View")
            set_iso_view = gtk.MenuItem("Iso View")
            enable_fourth_display = gtk.MenuItem("Enable A Axis Display")
            disable_fourth_display = gtk.MenuItem("Disable A Axis Display")
            set_front_view.connect("activate", self.set_front_view)
            set_top_view.connect("activate", self.set_top_view)
            set_side_view.connect("activate", self.set_side_view)
            set_iso_view.connect("activate", self.set_iso_view)
            enable_fourth_display.connect("activate", self.enable_fourth_axis_toolpath_display)
            disable_fourth_display.connect("activate", self.disable_fourth_axis_toolpath_display)
            menu.append(set_iso_view)
            menu.append(set_top_view)
            menu.append(set_front_view)
            menu.append(set_side_view)

            imperial = not self.ui.g21
            sml_text = "Grid 0.1 inch" if imperial else "Grid 5 mm"
            med_text = "Grid 0.5 inch" if imperial else "Grid 10 mm"
            lrg_text = "Grid 1.0 inch" if imperial else "Grid 25 mm"

            set_grid_size_small = gtk.MenuItem(sml_text)
            set_grid_size_med = gtk.MenuItem(med_text)
            set_grid_size_large = gtk.MenuItem(lrg_text)
            set_grid_size_none = gtk.MenuItem("No Grid")

            set_grid_size_small.connect("activate", self.set_grid_size_small)
            set_grid_size_med.connect("activate", self.set_grid_size_med)
            set_grid_size_large.connect("activate", self.set_grid_size_large)
            set_grid_size_none.connect("activate", self.set_grid_size_none)

            menu.append(set_grid_size_small)
            menu.append(set_grid_size_med)
            menu.append(set_grid_size_large)
            menu.append(set_grid_size_none)

            menu.append(enable_fourth_display)
            menu.append(disable_fourth_display)

            menu.popup(None, None, None, event.button, event.time)
            set_front_view.show()
            set_side_view.show()
            set_top_view.show()
            set_iso_view.show()

            if self.ui_view != 'p':
                set_grid_size_small.show()
                set_grid_size_med.show()
                set_grid_size_large.show()

            try:
                if self.ui.redis.hget('machine_prefs', 'enable_fourth_axis_toolpath') == 'True':
                    disable_fourth_display.show()
                else:
                    enable_fourth_display.show()
            except:
                enable_fourth_display.show()

    def set_current_ui_view(self):
        if self.ui_view == 'y':
            self.set_front_view()
        elif self.ui_view == 'x':
            self.set_side_view()
        elif self.ui_view == 'z':
            self.set_top_view()
        elif self.ui_view == 'p':
            self.set_iso_view()

    def set_front_view(self, widget=None):
        self.set_view_y()
        self.ui_view = 'y'
        self._redraw()
        return

    def set_side_view(self, widget=None):
        self.set_view_x()
        self.ui_view = 'x'
        self._redraw()
        return

    def set_top_view(self, widget=None):
        self.set_view_z()
        self.ui_view = 'z'
        self._redraw()
        return

    def set_iso_view(self, widget=None):
        self.set_view_p()
        self.ui_view = 'p'
        self._redraw()
        return

    def set_grid_size_small(self, widget):
        size = (5/25.4) if self.ui.g21 else .1
        self.set_grid_size(size)

    def set_grid_size_med(self, widget):
        size = (10/25.4) if self.ui.g21 else .5
        self.set_grid_size(size)

    def set_grid_size_large(self, widget):
        size = (25/25.4) if self.ui.g21 else 1.0
        self.set_grid_size(size)

    def set_grid_size_none(self, widget):
        self.set_grid_size(0.0)

    def enable_fourth_axis_toolpath_display(self, widget):
        self.ui.redis.hset('machine_prefs', 'enable_fourth_axis_toolpath', 'True')
        self.set_geometry('AXYZ')

    def disable_fourth_axis_toolpath_display(self, widget):
        self.ui.redis.hset('machine_prefs', 'enable_fourth_axis_toolpath', 'False')
        self.set_geometry('XYZ')


class jaGremlin(Tormach_Mill_Gremlin):
    def __init__(self, ja, width, height):
        Tormach_Mill_Gremlin.__init__(self, ja.conversational.ui, width, height)
        self.ja = ja
        self.current_view = 'p'
        self.spooler = None

    def report_gcode_warnings(self, warnings, filename, suppress_after = 3):
        print 'jaGremlin.report_gcode_warnings: file: %s, %d warnings' % (filename,len(warnings))

    def load_gcode_list(self, gcode_list):
        if self.initialised:
            path = TormachUIBase.gcode_list_to_tmp_file(gcode_list)
            if path is not None:
                self.load(path)
                self.queue_draw()
            self.spooler = None
        else:
            self.spooler = gcode_list

    def realize(self,widget):
        super(jaGremlin, self).realize(widget)
        if self.spooler is not None:
            self.load_gcode_list(self.spooler)
            self.set_default_view()
            self.queue_draw()

    def set_default_view(self):
        self.current_view = self.ui_view = 'p'
        if self.initialised:
            self.set_current_view()

import signal
def SIGINT_handler(signal, frame):
    print("Can't shut down via Ctrl-C, please use exit button instead")

signal.signal(signal.SIGINT, SIGINT_handler)



if __name__ == "__main__":
    # unbuffer stdout so print() shows up in sync with other output
    # the pipe from the redirect in operator_login causes buffering
    sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', 0)
    UI = mill()
    screen_width = gtk.gdk.Screen().get_width()
    screen_height = gtk.gdk.Screen().get_height()
    print 'screen resolution is now %d x %d' % (screen_width, screen_height)
    if screen_width > 1024 and screen_height > 768:
        UI.window.set_decorated(True)

    # always connect to 'delete_event' in case Alt-F4 isn't disabled in keyboard shortcuts
    UI.window.connect('delete_event', UI.delete_event)
    UI.window.resize(1024, 768)
    UI.notebook.set_current_page(0)
    UI.probe_notebook.set_current_page(0)
    UI.gremlin.set_view_p()
    UI.kill_splash_screen()
    gtk.main()
    sys.exit(UI.program_exit_code)


