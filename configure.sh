#!/usr/bin/env bash

CALLDIR=$(pwd)

configure_coqeal_theory() {
	echo "Building Makefile for CoqEAL.theory..."
	coq_makefile -f _CoqProject_theory -o Makefile.theory
	return $?
}

configure_coqeal_refinements() {
	echo "Building Makefile for CoqEAL.refinements..."
	coq_makefile -f _CoqProject_refine -o Makefile.refine
	return $?
}

configure_coqeal_theory && configure_coqeal_refinements
