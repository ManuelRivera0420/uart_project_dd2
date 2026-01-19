src=uart_top
testname=test
verbosity=UVM_MEDIUM
.DEFAULT_GOAL := help

list:
	@echo "# rtl" > list.f
	@test -f ../rtl/${src}.sv && echo "../rtl/${src}.sv" >> list.f
	@echo "# verification" >> list.f
	@echo "../verif/${src}_tb.sv" >> list.f
	
ana:
	xvlog -sv -f list.f -L uvm
elab: ana
	xelab -debug typical --relax ${src}_tb
sim: elab
	xsim work.${src}_tb -runall

waves: elab
	xsim work.${src}_tb -gui -tclbatch waves.tcl &

sim_gui: elab
	xsim work.${src}_tb -runall -gui
cov: 
	xcrg -report_format html -dir xsim.covdb
sim_uvm: elab
	xsim work.${src}_tb "UVM_TESTNAME=${testname}"
help:
	
sim_uvm_gui: elab
	xsim work.${src}_tb -gui "UVM_TESTNAME=${testname}"
help:
	@echo ""
	@echo "==== Basic Vivado Compile/Simulator makefile ======"
	@echo " Targets:"
	@echo " ana    --> Analyzes the HDL file with xvlog command"
	@echo " elab   --> Elaborates de design with xelab command"
	@echo " sim    --> Simulates the design with xsim command"
	@echo " clean  --> Clean support files"
	@echo " help   --> this help menu =)"
	@echo ""
clean:
	rm -rf xvlog* xelab* xsim* webtalk* tr_db* .Xil vivado* work* xsim.dir
	@echo "wcfg preserved"
	rmdir /s /q xsim.dir
