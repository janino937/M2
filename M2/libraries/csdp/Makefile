CSDP_VERSION = 6.2.0
LIBNAME = Csdp
VERSION = $(CSDP_VERSION)
PATCHFILE = /home/colab/M2/M2/libraries/csdp/patch-$(CSDP_VERSION)
URL = http://www.coin-or.org/download/source/Csdp
#URL = http://macaulay2.com/Downloads/OtherSourceCode
TARFILE = Csdp-$(VERSION).tgz

CONFIGURECMD = true
BUILDOPTIONS = CC="$(CC) $(OPENMP_CXXFLAGS)" CXX="$(CXX) $(OPENMP_CXXFLAGS)" LDFLAGS="$(LDFLAGS) $(OPENMP_CXXFLAGS)" LDLIBS="$(LDLIBS) " #PREFIX=/nowhere
#INSTALLOPTIONS = PREFIX=$(LIBRARIESDIR)

# the test uses too much memory, leading to "libgomp: Thread creation failed: Resource temporarily unavailable", so we disable it
#CHECKTARGET = unitTest
CHECKTARGET = .

LICENSEFILES = LICENSE README
PROGRAMS = solver/csdp
STRIPFILES = $(PROGRAMS) theta/complement theta/graphtoprob theta/rand_graph theta/theta

#$(info BUILDOPTIONS is $(BUILDOPTIONS))

include ../Makefile.library
Makefile: ./Makefile.in ; cd ../.. && ./config.status libraries/csdp/Makefile
# Local Variables:
# compile-command: "make -C $M2BUILDDIR/libraries/csdp "
# End:
