This is a workbench for a new type hole inference algorithm. 

TODOs:
- Test in more cases
- Deal with cyclic constraints
- Compress set of alternative solutions, folding duplicates
- Clean up the code: put the map in a module to section off the conversion of provenances to strings for map lookup
- Improve the efficiency of the data structures at play - e.g. incrementalize the provenance map so it isn't recomputed after each solution
- Put the suggestions back in the surface syntax for the user to look at and select (or, maybe not worth it for proof of concept)