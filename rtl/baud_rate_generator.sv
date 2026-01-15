`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Manuel Enrique Rivera Acosta
// 
// Create Date: 10/28/2025 11:14:06 AM
// Design Name: 
// Module Name: baud_rate_generator
// Project Name: 
//////////////////////////////////////////////////////////////////////////////////

module baud_rate_generator #(parameter CLK_FREQ =50_000_000)(
    input  logic       clk,
    input  logic       arst_n,
    input  logic [3:0] baud_sel,
    output logic       tick
);

/*
localparam int BAUD_TABLE [0:12] = {
    1200,
    2400,
    4800,
    9600,
    19200,
    28800,
    38400,
    57600,
    76800,
    115200,
    230400,
    460800,
    921600
};

*/


logic [31:0] counter_max;
logic [31:0] counter;

/*
always_comb begin
    if (baud_sel <= 4'd12)
        counter_max = (CLK_FREQ / (BAUD_TABLE[baud_sel] * 16)) - 1;
    else
        counter_max = (CLK_FREQ / (BAUD_TABLE[0] * 16)) - 1; // default
end
*/

assign counter_max = (CLK_FREQ / (9600 * 16));

always_ff @(posedge clk or negedge arst_n) begin
    if(!arst_n) begin
        tick    <= 1'b0;
        counter <= 32'd0;
    end else begin
        if (counter == counter_max) begin
            counter <= 32'd0;
            tick    <= 1'b1;
        end else begin
            counter <= counter + 1;
            tick    <= 1'b0;
        end
    end
end

endmodule
