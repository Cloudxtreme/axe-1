#!/usr/bin/env python

#!/bin/bash
#
# Copyright (c) 2015 Matthew Naylor
# All rights reserved.
#
# This software was developed by SRI International and the University of
# Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-10-C-0237
# ("CTSRD"), as part of the DARPA CRASH research programme.
#
# This software was developed by SRI International and the University of
# Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-11-C-0249
# ("MRC2"), as part of the DARPA MRC research programme.
#
# @BERI_LICENSE_HEADER_START@
#
# Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
# license agreements.  See the NOTICE file distributed with this work for
# additional information regarding copyright ownership.  BERI licenses this
# file to you under the BERI Hardware-Software License, Version 1.0 (the
# "License"); you may not use this file except in compliance with the
# License.  You may obtain a copy of the License at:
#
#   http://www.beri-open-systems.org/legal/license-1-0.txt
#
# Unless required by applicable law or agreed to in writing, Work distributed
# under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations under the License.
#
# @BERI_LICENSE_HEADER_END@
#

import matplotlib.pyplot as plt
import numpy as np
import sys

if len(sys.argv) != 3:
  print "usage: plot.py [input.txt] [output.png]"
  sys.exit()

X=[]
Y=[]
with open(sys.argv[1]) as f:
  for line in f:
    fields = line.split()
    X.append(float(fields[0]))
    Y.append(float(fields[1][:-1]))

fig = plt.figure()
ax = fig.add_subplot(111)
ax.spines['top'].set_color('none')
ax.spines['right'].set_color('none')
ax.yaxis.set_ticks_position('left')
ax.xaxis.set_ticks_position('bottom')

plt.xticks(fontsize=12)
plt.yticks(fontsize=12)
plt.margins(0.1)

plt.xlim([0,34000])
plt.ylim([0,15])

plt.ylabel("Time (s)", fontsize=14)
plt.xlabel("\nNumber of instructions", fontsize=14)

plt.plot(X[0:], Y[0:], 'b.')

#plt.show()
plt.savefig(sys.argv[2])
