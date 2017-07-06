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
	if [[ ! -f Makefile.theory ]]; then
		coq_makefile -f _CoqProject_theory -o Makefile.theory
	fi
	echo "Installing CoqEAL.theory..."
	make -f Makefile.theory && make install -f Makefile.theory && \
		echo "Installation complete!"
	return $?
}

install_coqeal_refinements() {
	if [[ ! -f Makefile.refine ]]; then
		coq_makefile -f _CoqProject_refine -o Makefile.refine
	fi
	echo "Installing CoqEAL.refinements..."
	make -f Makefile.refine && make install -f Makefile.refine && \
		echo "Installation complete!"
	return $?
}

install_paramcoq && install_coqeal_theory && install_coqeal_refinements
