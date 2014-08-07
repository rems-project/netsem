SHELL=bash
.SUFFIXES:

################################################################################
# export Spec1 and Spec3 in a single tarball

# want to use the sub makes
all:
	rm -rf tarball-Spec-1-and-3-public*
	rm -rf Spec1/tarball-Spec1-public*
	rm -rf Spec3/tarball-Spec3-public*
	mkdir tarball-Spec-1-and-3-public
	#cd Spec1 && Holmake HolDoc.sml HolDoc.sig && make tarball-Spec1-public
	cd Spec1 && make tarball-Spec1-public
	cd Spec3 && make tarball-Spec3-public
	mv Spec1/tarball-Spec1-public/Spec1 tarball-Spec-1-and-3-public
	mv Spec3/tarball-Spec3-public/Spec3 tarball-Spec-1-and-3-public
	cp README tarball-Spec-1-and-3-public
	cp LICENSE-spec-public tarball-Spec-1-and-3-public
	tar -cvz -f tarball-Spec-1-and-3-public.tar.gz tarball-Spec-1-and-3-public

install:
	cp tarball-Spec-1-and-3-public.tar.gz ~/public_html/Netsem
