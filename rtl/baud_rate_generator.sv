`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Manuel Enrique Rivera Acosta
// 
// Create Date: 10/28/2025 11:14:06 AM
// Design Name: 
// Module Name: baud_rate_generator
//////////////////////////////////////////////////////////////////////////////////

// Baud Rate Generator
// - Generates a periodic tick for UART timing
// - Tick frequency = baud rate × 16 (oversampling)

module baud_rate_generator #(parameter CLK_FREQ =100_000_000)(
    input  logic clk,      // System clock
    input  logic arst_n,    // Asynchronous active-low reset
    output logic tick      // Oversampling tick output
);

// Maximum counter value to generate baud x16 tick
logic [31:0] counter_max;
// variable to store counter
logic [31:0] counter;

// Compute divider for 9600 baud with x16 oversampling
assign counter_max = (CLK_FREQ / (9600 * 16));

// Counter-based tick generation
always_ff @(posedge clk or negedge arst_n) begin
    if(!arst_n) begin
        tick    <= 1'b0;
        counter <= 32'd0;
    end else begin
        if (counter == counter_max) begin
            counter <= 32'd0;
            tick    <= 1'b1; // Assert tick for one clock cycle
        end else begin
            counter <= counter + 1;
            tick    <= 1'b0;
        end
    end
end

endmodule
