#!/usr/bin/python
import sys
import os
import re
from collections import OrderedDict

# CHANGE rootdir to location of oscar git repo
rootdir="/home/rrusk/git/oscar/src"
# ASSUMES file containing properties not found is in same directory as this Python script
propertyList="./not_found.txt"

def load_properties(filepath):
  props = OrderedDict()
  with open(filepath, "rt") as f:
    for line in f:
      props[line.strip()] = ""
  return props

def word_find(line):
  pat = re.compile(r'\b[\w\.]+\b')
  return re.findall(pat, line)

def word_find2(line):
  return list(line.strip().split('"'))

def find_property(property):
  for dirpath, dirnames, files in os.walk(rootdir):
    for filename in files:
      with open(os.path.join(dirpath, filename), 'r') as fin:
        print_filename=True
        line_number=0
        for line in fin:
          line_number=line_number+1
          if property=="program" or property=="host" or property=="plugin":
            results = word_find2(line)
          else:
            results = word_find(line)
          if property in results:
            if print_filename:
              print "  ---",os.path.join(dirpath,filename)
              print_filename=False
            if len(line.strip()) < 400:
              print line_number,': ',line.rstrip()
            else:
              print line_number,': ','line too long: ',len(line),' characters'
            #break

properties = load_properties(propertyList)
for property in properties:
  print "Property =>", property
  sys.stdout.flush()
  find_property(property)
