#!/usr/bin/env python2
# coding: latin-1
#
#
# Module for probing routines
#
# "©2012 Tormach® LLC. All rights reserved."
#

# for debugging within Wing IDE
#import wingdbstub

import time
import sys
import gtk
import math
from constants import *
import linuxcnc


PROBING_TIMEOUT = 200
G_ZERO_TIMEOUT = 200
CLEAR_DIST_OFFSET = 0.25
PROBE_SEARCH_INCREMENT = 0.50
X_Y_PROBE_OFFSET = 0.30


def execute_probe_oword(self, oword, needs_tip_dia=False):
    if self.status.probe_val:
        self.error_handler.write("Cannot start probe move with probe tripped.  Please check probe polarity on Settings page before continuing.")
        return 
    if (self.status.tool_in_spindle != MILL_PROBE_TOOL_NUM):
        self.error_handler.write("Must change tools to tool %s before probing." % MILL_PROBE_TOOL_NUM)
        return  
    if needs_tip_dia:
        if self.status.tool_table[MILL_PROBE_TOOL_NUM].diameter <= 0.001:
            self.error_handler.write("This probe routine requires a valid tip diameter for the probe tool.  Please enter a valid probe tip diameter in the diameter column of the tool table for tool %s." % MILL_PROBE_TOOL_NUM)
            return

    feedrate = check_max_feedrate(self)
    self.issue_mdi(oword + 'call [%f]' % (feedrate))
    
def execute_ets_oword(self, oword):
    if self.status.probe_val:
        self.error_handler.write("Cannot start ETS move with ETS tripped.  Please check probe polarity on Settings page before continuing.")
        return     
    feedrate = check_max_feedrate(self)
    g21_scalar = 1
    if self.status.gcodes[5] == 210: g21_scalar = 25.4    
    ets_height = self.ets_height * g21_scalar
    limit = self.status.axis[2]['min_position_limit']
    self.issue_mdi(oword + 'call [%f] [%f] [%f]' % (feedrate, ets_height, limit))
    
def execute_probe_setup_oword(self, oword):
    if self.status.probe_val:
        self.error_handler.write("Cannot start probe or ETS move with probe tripped.  Please check probe polarity on Settings page before continuing.")
        return       
    feedrate = check_max_feedrate(self)
    g21_scalar = 1
    if self.status.gcodes[5] == 210: g21_scalar = 25.4
    
    ref_surface = g21_scalar * self.probe_setup_reference_surface
    limit = self.status.axis[2]['min_position_limit']
    self.issue_mdi(oword + 'call [%f] [%f] [%f]' % (feedrate, ref_surface, limit))

def check_probe_ready(self):
    okay = False
    if self.status.probe_val:
        self.error_handler.write("Cannot start probe move with probe tripped.  Please check probe polarity on Settings page before continuing.")
        return okay
    if (self.status.tool_in_spindle != MILL_PROBE_TOOL_NUM):
        self.error_handler.write("Must change tools to tool %s before probing." % MILL_PROBE_TOOL_NUM)
        return okay
    okay = True
    return okay

def check_probe_dia(self):
    okay = False
    if self.status.tool_table[MILL_PROBE_TOOL_NUM].diameter <= 0.001:
        self.error_handler.write("This probe routine requires a valid tip diameter for the probe tool.  Please enter a valid probe tip diameter in the diameter column of the tool table for tool %s." % MILL_PROBE_TOOL_NUM)
        return okay
    okay = True
    return okay

def find_corner(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    xlimit = self.status.axis[0]['max_position_limit']
    ylimit = self.status.axis[1]['max_position_limit']
    self.issue_mdi('o<probe_corner> call [%f] [%f] [%f]' % (feedrate, xlimit, ylimit))

def find_x_plus_origin(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[0]['max_position_limit']
    self.issue_mdi('o<probe_x_plus_origin> call [%f] [%f]' % (feedrate, limit))

def find_x_minus_origin(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[0]['min_position_limit']
    self.issue_mdi('o<probe_x_minus_origin> call [%f] [%f]' % (feedrate, limit))

def find_y_plus_origin(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[1]['max_position_limit']
    self.issue_mdi('o<probe_y_plus_origin> call [%f] [%f]' % (feedrate, limit))

def find_y_minus_origin(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[1]['min_position_limit']
    self.issue_mdi('o<probe_y_minus_origin> call [%f] [%f]' % (feedrate, limit))

def find_z_minus_origin(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    # tip dia not required for Z
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[2]['min_position_limit']
    self.issue_mdi('o<probe_z_minus_origin> call [%f] [%f]' %
                   (feedrate, limit))

def find_pocket_center(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    # tip dia not required for finding centers
    feedrate = check_max_feedrate(self)
    xmaxlimit = self.status.axis[0]['max_position_limit']
    xminlimit = self.status.axis[0]['min_position_limit']
    ymaxlimit = self.status.axis[1]['max_position_limit']
    yminlimit = self.status.axis[1]['min_position_limit']
    self.issue_mdi('o<probe_pocket> call [%f] [%f] [%f] [%f] [%f]' % (feedrate, xmaxlimit, xminlimit, ymaxlimit , yminlimit))

def find_pocket_x_center(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    # tip dia not required for finding centers
    feedrate = check_max_feedrate(self)
    xmaxlimit = self.status.axis[0]['max_position_limit']
    xminlimit = self.status.axis[0]['min_position_limit']
    self.issue_mdi('o<probe_pocket_x> call [%f] [%f] [%f]' % (feedrate, xmaxlimit, xminlimit))

def find_pocket_y_center(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    # tip dia not required for finding centers
    feedrate = check_max_feedrate(self)
    ymaxlimit = self.status.axis[1]['max_position_limit']
    yminlimit = self.status.axis[1]['min_position_limit']
    self.issue_mdi('o<probe_pocket_y> call [%f] [%f] [%f]' % (feedrate, ymaxlimit, yminlimit))

def find_work_z(self):
    find_z_minus(self)

def find_rect_boss_center(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    # tip dia not required for finding centers
    feedrate = check_max_feedrate(self)
    xmaxlimit = self.status.axis[0]['max_position_limit']
    xminlimit = self.status.axis[0]['min_position_limit']
    ymaxlimit = self.status.axis[1]['max_position_limit']
    yminlimit = self.status.axis[1]['min_position_limit']
    self.issue_mdi('o<probe_boss> call [%f] [%f] [%f] [%f] [%f]' %
                   (feedrate, xmaxlimit, xminlimit, ymaxlimit , yminlimit))

def find_circ_boss_center(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)  # only used in stepover calculation
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    xmaxlimit = self.status.axis[0]['max_position_limit']
    xminlimit = self.status.axis[0]['min_position_limit']
    ymaxlimit = self.status.axis[1]['max_position_limit']
    yminlimit = self.status.axis[1]['min_position_limit']
    self.issue_mdi('o<probe_boss_circ> call [%f] [%f] [%f] [%f] [%f]' %
                   (feedrate, xmaxlimit, xminlimit, ymaxlimit , yminlimit))

def find_x_plus(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[0]['max_position_limit']
    self.issue_mdi('o<probe_x_plus> call [%f] [%f]' % (feedrate, limit))

def find_x_minus(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[0]['min_position_limit']
    self.issue_mdi('o<probe_x_minus> call [%f] [%f]' % (feedrate, limit))

def find_y_plus(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[1]['max_position_limit']
    self.issue_mdi('o<probe_y_plus> call [%f] [%f]' % (feedrate, limit))

def find_y_minus(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[1]['min_position_limit']
    self.issue_mdi('o<probe_y_minus> call [%f] [%f]' % (feedrate, limit))

def find_y_plus_a(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[1]['max_position_limit']
    self.issue_mdi('o<probe_y_plus_a> call [%f] [%f]' % (feedrate, limit))

def find_y_plus_b(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[1]['max_position_limit']
    self.issue_mdi('o<probe_y_plus_b> call [%f] [%f]' % (feedrate, limit))

def find_y_plus_c(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[1]['max_position_limit']
    self.issue_mdi('o<probe_y_plus_c> call [%f] [%f]' % (feedrate, limit))

def find_z_minus(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    feedrate = check_max_feedrate(self)
    limit = self.status.axis[2]['min_position_limit']
    self.issue_mdi('o<probe_z_minus> call [%f] [%f]' % (feedrate, limit))

def find_a_axis_center(self):
    ready = check_probe_ready(self)
    if not ready:
        return
    tip_okay = check_probe_dia(self)
    if not tip_okay:
        return
    feedrate = check_max_feedrate(self)
    ymaxlimit = self.status.axis[1]['max_position_limit']
    yminlimit = self.status.axis[1]['min_position_limit']
    zmaxlimit = self.status.axis[2]['max_position_limit']
    zminlimit = self.status.axis[2]['min_position_limit']
    self.issue_mdi('o<probe_find_a_axis_center> call [%f] [%f] [%f] [%f] [%f]' %
                   (feedrate, ymaxlimit, yminlimit, zmaxlimit , zminlimit))
  
    
def move_and_set_probe_length(self):
    execute_probe_setup_oword(self, 'o<probe_move_and_set_probe_length>')

def move_and_set_sensor_height(self):  # TODO - I don't think this is used anywhere
    execute_probe_setup_oword(self, 'o<probe_move_and_set_sensor_height>')

def move_and_set_tool_length(self):
    execute_ets_oword(self, 'o<probe_move_and_set_tool_length>')

def find_work_z_with_ets(self):
    execute_ets_oword(self, 'o<probe_find_work_z_with_ets>')

def check_max_feedrate(self):
    g21_scalar = 1
    if self.status.gcodes[5] == 210: g21_scalar = 25.4
        
    # check for appropriate feedrate
    feedrate = abs(self.status.settings[1])
        
    max_probing_feedrate = MAX_PROBING_FEEDRATE * g21_scalar
        
    if feedrate > max_probing_feedrate:
        self.error_handler.write("Current feedrate too high for probing - feedrate must be less than %i inches per minute to use probing buttons.  Setting feedrate to 10 IPM." % MAX_PROBING_FEEDRATE, ALARM_LEVEL_LOW)
        feedrate = DEFAULT_PROBING_FEEDRATE * g21_scalar

    # if feedrate is zero, default to 10 IPM
    if feedrate == 0:
        feedrate = DEFAULT_PROBING_FEEDRATE * g21_scalar
        
    return feedrate
