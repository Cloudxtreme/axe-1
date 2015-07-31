### A checker for SPARC memory consistency

Axe is a tool that checks memory traces (consisting of load, store,
atomic read-modify-write, and memory barrier instructions) against the
SPARC memory consistency models: *sequential consistency* (SC), *total
store order* (TSO), *partial store order* (PSO) and *relaxed memory
order* (RMO).  It was built to help test the shared memory subsystem
of the BERI multiprocessor, but could be used to test other memory
subsystems too.  It is written in Haskell and uses the Yices
constraint solver.

Axe is explained in more detail in [this
report](https://github.com/CTSRD-CHERI/axe/raw/master/doc/report.pdf).

### Dependencies

Ubuntu/Debian packages:

    sudo apt-get install ghc haskell-platform pandoc

Also download [Yices](http://yices.csl.sri.com/) (version 2.3.1 or
later) and make sure it is in your path.
