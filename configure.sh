#!/usr/bin/env bash

CALLDIR=$(pwd)

install_paramcoq() {
	echo -n "Installing paramcoq..."
	cd paramcoq && make && make install && \
		echo "Installation complete!"
	if [ $? -eq 0 ]; then
		cd ${CALLDIR} && return 0
	else
		cd ${CALLDIR} && return 1
	fi
}

install_coqeal_theory() {
	echo "Installing CoqEAL.theory..."
	coq_makefile -f _CoqProject_theory -o Makefile.theory
	make -f Makefile.theory && make install -f Makefile.theory && \
		echo "Installation complete!"
	return $?
}

install_coqeal_refinements() {
	echo "Installing CoqEAL.refinements..."
	coq_makefile -f _CoqProject_refine -o Makefile.refine
	make -f Makefile.refine && make install -f Makefile.refine && \
		echo "Installation complete!"
	return $?
}

install_paramcoq && install_coqeal_theory && install_coqeal_refinements
