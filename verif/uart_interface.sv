`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: Mifral
// Engineer:
//
// Design Name: semicolab
// Module Name: interface_ip_tile
//
//////////////////////////////////////////////////////////////////////////////////

interface uart_interface(input logic clk, input logic arst_n);

// CSR parameters
parameter BYTE_WIDTH = 8;
parameter BIT_SAMPLING = 15;
parameter HALFBIT_SAMPLING = 7;

// Declaration of signals used by the uart
logic [BYTE_WIDTH - 1 : 0] data_out;
logic [BYTE_WIDTH - 1 : 0] data_in;
logic tx_start;
logic tx_done;
logic rx_done;

// modport
modport user_tile_modport(
	input data_in, tx_start,
	output data_out, tx_done, rx_done
);

// task to write data from the transmitter into the receiver
task write_data_in(logic [BYTE_WIDTH - 1 : 0] data);
	@(posedge clk);
	data_in <= data;
    @(posedge clk);
    tx_start <= 1'b1;
    @(posedge clk);
    tx_start <= 1'b0;
endtask

endinterface
