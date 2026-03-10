# =============================================================================
# Targets:
#   make sim_top        — full top-level integration test (needs complete DUT)
#   make waves_top      — open top-level waveforms in GTKWave
#   make clean          — remove all build artifacts
# =============================================================================
VERILATOR  = verilator
GTKWAVE    = gtkwave
PYTHON     = python3

RTL_DIR    = ../src
TB_DIR     = ../tb

VFLAGS = --binary --timing --assert --trace --coverage -Wall \
         -Wno-DECLFILENAME -Wno-UNUSED

RTL_SRCS = \
    $(RTL_DIR)/qcldpcPkg.sv \
    $(RTL_DIR)/pipelinedCircularShifter.sv \
    $(RTL_DIR)/ProtoMatrixRom.sv \
    $(RTL_DIR)/top.sv

TB_PKG = $(TB_DIR)/qcldpcTBPkg.sv

TB_SRCS = \
    $(TB_DIR)/qcldpcDriver.sv \
    $(TB_DIR)/qcldpcMonitor.sv \
    $(TB_DIR)/qcldpcScoreboard.sv \
    $(TB_DIR)/qcldpcCoverage.sv \
    $(TB_DIR)/qcldpcTBTop.sv

# Full integration test — requires complete DUT
.PHONY: sim_top
sim_top: obj_dir_top/sim_top
	@echo ""
	@echo "Running full integration test..."
	@echo "--------------------------------"
	./obj_dir_top/sim_top
	@echo ""

obj_dir_top/sim_top: $(RTL_SRCS) $(TB_PKG) $(TB_SRCS)
	$(VERILATOR) $(VFLAGS) \
	    -I$(RTL_DIR) \
	    $(RTL_SRCS) \
	    $(TB_PKG) \
	    $(TB_SRCS) \
	    --top-module qcldpcTBTop \
	    -Mdir obj_dir_top \
	    -o sim_top

# Waveform viewing
.PHONY: waves_top
waves_top: waves.vcd
	$(GTKWAVE) waves.vcd &

# Coverage report — annotates source files showing which lines were hit
.PHONY: coverage
coverage:
	@if [ -f coverage.dat ]; then \
	    verilator_coverage --annotate coverage_annotated coverage.dat; \
	    echo "Coverage report written to coverage_annotated/"; \
	else \
	    echo "No coverage.dat found — run sim_top first"; \
	fi

# Clean
.PHONY: clean
clean:
	rm -rf obj_dir_shifter obj_dir_top
	rm -f waves.vcd waves_shifter.vcd
	rm -f coverage.dat
	rm -rf coverage_annotated
	@echo "Clean complete"