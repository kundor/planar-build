CCFLAGS= -std=gnu++14 -Wall -Wextra 
OFLAGS= -O2 -march=native 
DFLAGS= -ggdb -DINFO_LVL=3 -DFLUSH

planar: planar.cc nausparse.h nauty.h nauty.a
	$(CXX) $(CCFLAGS) $(OFLAGS) -DMAX_FACES=22 $< nauty.a -o $@

planar-db: planar.cc nausparse.h nauty.h nauty.a
	$(CXX) $(CCFLAGS) $(DFLAGS) $< nauty.a -o $@

planar-fast: planar-fast.cc nausparse.h nauty.h nauty.a
	$(CXX) $(CCFLAGS) $(OFLAGS) -DMAX_FACES=34 $< nauty.a -o $@

