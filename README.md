% Matthew Naylor
% University of Cambridge
% June 2015

Axe is a tool that checks memory traces (consisting of load, store,
atomic read-modify-write, and memory barrier instructions) against the
SPARC memory consistency models: *sequential consistency* (SC), *total
store order* (TSO), partial store order (PSO) and *relaxed memory
order* (RMO).  It was built to help verify the shared memory subsystem
of the BERI multiprocessor, but could be used to verify other memory
subsystems too.  It is written in Haskell and uses the Yices
constraint solver.

Axe is explained in more detail in this [report](doc/report.pdf).

Dependencies
============

Ubuntu/Debian packages:

    sudo apt-get install ghc
    sudo apt-get install haskell-platform
    sudo apt-get install pandoc

Also download Yices (version 2.3.1 or later) and make sure it is in
your path:

    http://yices.csl.sri.com/
