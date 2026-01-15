`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Manuel Enrique Rivera Acosta
// 
// Create Date: 10/28/2025 12:14:17 PM
// Design Name: 
// Module Name: uart_top
//////////////////////////////////////////////////////////////////////////////////

//`include "../defines.svh"

module uart_top (
    input logic clk,
    input logic arst_n,
    input logic rx,
	 input logic next_program,
    input logic [BAUD_SEL_SIZE - 1 : 0] baud_sel,
    input logic [ADDR_WIDTH - 1 : 0] rdaddr,
    output logic prog_rdy,
    output logic rx_done,
    output logic [DATA_WIDTH - 1 : 0] data_out,
    output logic [((DATA_WIDTH / 4) * 7) - 1 : 0] display,
    output logic [DATA_WIDTH - 1 : 0] read_data,
    output logic tx,
	 output logic ready,
	 output logic [3:0] state,
	 output logic busy,
    output logic tx_done,
    input logic tx_start
);

logic tick;
logic inst_rdy;
logic [BYTE_WIDTH - 1 : 0] uart_byte;
logic [ADDR_WIDTH - 1 : 0] wr_addr;
logic [BYTE_WIDTH - 1 : 0] n_instructions;
 
shift_register_fsm #(.BYTE_WIDTH(BYTE_WIDTH), .ADDR_WIDTH(ADDR_WIDTH)) shift_register_fsm_i(
    .clk (clk),
    .arst_n (arst_n),
	 .next_program(next_program),
    .w_en (rx_done), // input write enable coming from uart rx_done
    .data_in (uart_byte), // data_in coming from uart data_out port
    .data_out (data_out), // data out to be written in the program memory after receiving 4 bytes from uart
    .wr_addr (wr_addr), // write addres for the memory
    .inst_rdy (inst_rdy), // flag to indicate that a instruction is ready, this is the write enable for the memory
	 .n_instructions(n_instructions),
	 .busy(busy),
	 .state(state),
	 .ready(ready),
    .prog_rdy (prog_rdy)  // flag to indicate that the program has been initialized into the memory
);


baud_rate_generator #(.CLK_FREQ(CLK_FREQ)) baud_rate_generator_i(
    .clk(clk),
    .arst_n(arst_n),
    .tick(tick),
    .baud_sel(baud_sel)
);

transmitter #(.BYTE_WIDTH(BYTE_WIDTH)) transmitter_i(
   .clk(clk),
   .arst_n(arst_n),
   .data_in(8'd10),
   .tick(tick),
   .tx_start(rx_done),
   .tx(tx),
   .tx_done(tx_done)
);
 
display_7_segments #(.DATA_WIDTH(DATA_WIDTH)) display_7_segments_i(
    .data_in (read_data),
    .display (display)
);
 
receiver #(.BYTE_WIDTH(BYTE_WIDTH)) receiver_i(
.clk(clk),
.arst_n(arst_n),
.tick(tick),
.rx(rx), // RX CONNECTED TO THE TX FROM THE TRANSMITTER MODULE
.rx_done(rx_done),
.data_out(uart_byte)
);

instruction_memory #(.BYTE_WIDTH(BYTE_WIDTH), .ADDR_WIDTH(ADDR_WIDTH), .MEM_DEPTH(MEM_DEPTH), .DATA_WIDTH(DATA_WIDTH)) instruction_memory_i(
.clk(clk),
.rd_addr(rdaddr),
.rd_data(read_data),
.data_in(data_out),
.wr_addr(wr_addr),
.w_en(inst_rdy)
);


endmodule