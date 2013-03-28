# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

# Constants for gl rendering of enriched are collected here.

epsilon = 0.0001

min_unit_divider_length = 10.0
conj_increase = 72.0
conj_clause_spacing = 30.0
quantifier_variables_spacing = 80.0
quantifier_before_divider_spacing = 10.0
quantifier_after_divider_spacing = 55.0
exponential_border_width = 40.0

notThickness = 12.0
notShiftThickness = notThickness + 11.0
# Amount by which to shift the value contained inside a enriched.Not.
notShiftOffset = [notShiftThickness, notShiftThickness, 0.0]

# Consider making short dividers much narrower.
def widthOfDividerByLength(length):
  return 20.0

# Consider making short dividers much narrower.
def widthOfQuantifierDividerByLength(length):
  return 15.0

# Consider
def capLengthOfDividerByLength(length):
  return min(35.0, length / 7.0)
