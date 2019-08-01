HOMEPAGE = http://wwwth.mpp.mpg.de/members/bjurke/cohomcalg/
HOMEPAGE = http://wwwth.mppmu.mpg.de/members/blumenha/cohomcalg/
URL = http://macaulay2.com/Downloads/OtherSourceCode
VERSION = 031b
BUILDOPTIONS := CC="gcc" CXX="g++" LD="g++" CFLAGS="$(CFLAGS)"
TARFILE = cohomCalg-$(VERSION).zip
UNTARCMD = unzip $(TARFILE_DIR)/$(TARFILE)
LICENSEFILES = "GPLv3 License.txt"
CHECKTARGET = .
CONFIGURECMD = :
INSTALLCMD = :
PROGRAMS = bin/cohomcalg
STRIPFILES = $(PROGRAMS)
TARDIR = .
include ../Makefile.library
Makefile: ./Makefile.in ; cd ../.. && ./config.status libraries/cohomcalg/Makefile
# Local Variables:
# mode: makefile-gmake
# compile-command: "make -C $M2BUILDDIR/libraries/cohomcalg "
# End:
