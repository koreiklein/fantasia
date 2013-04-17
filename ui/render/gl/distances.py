# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

# Constants for gl rendering of basic are collected here.

from ui.render.gl import colors

epsilon = 0.0001

divider_spacing = 15.0

notThickness = 12.0
notShiftThickness = notThickness + 11.0
# Amount by which to shift the value contained inside a Not.
notShiftOffset = [notShiftThickness, notShiftThickness, 0.0]

quantifier_variables_spacing = 80.0
enriched_variable_binding_spacing = 80.0
quantifier_before_divider_spacing = 10.0
quantifier_after_divider_spacing = 55.0

exponential_border_width = 40.0

min_unit_divider_length = 100.0

min_intersect_divider_length = 250.0

unit_width = 20.0

quantifier_divider_width = 20.0

conjunctiveDividerWidth = 20.0

def capLengthOfDividerByLength(length):
  return min(35.0, length / 7.0)

inject_spacing = 8.0

before_dot_spacing = 8.0
after_dot_spacing = 8.0

dotWidth = 15.0
