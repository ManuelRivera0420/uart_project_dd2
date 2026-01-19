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

module uart_top #(parameter CLK_FREQ = 100_000_000, BYTE_WIDTH = 8) (
    input logic clk,
    input logic arst_n,
    input logic [BYTE_WIDTH - 1 : 0] data_in,
    input logic tx_start,
    output logic tx_done,
    output logic rx_done,
    output logic [BYTE_WIDTH - 1 : 0] data_out
);

logic tick;
logic serial_data;

baud_rate_generator #(.CLK_FREQ(CLK_FREQ)) baud_rate_generator_i(
    .clk(clk),
    .arst_n(arst_n),
    .tick(tick)
);

transmitter #(.BYTE_WIDTH(BYTE_WIDTH)) transmitter_i(
   .clk(clk),
   .arst_n(arst_n),
   .data_in(data_in),
   .tick(tick),
   .tx_start(tx_start),
   .tx(serial_data),
   .tx_done(tx_done)
);
 
receiver #(.BYTE_WIDTH(BYTE_WIDTH)) receiver_i(
.clk(clk),
.arst_n(arst_n),
.tick(tick),
.rx(serial_data), // RX CONNECTED TO THE TX FROM THE TRANSMITTER MODULE
.rx_done(rx_done),
.data_out(data_out)
);


endmodule
