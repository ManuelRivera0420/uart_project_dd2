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

module baud_rate_generator #(parameter CLK_FREQ =100_000_000)(
    input  logic       clk,
    input  logic       arst_n,
    output logic       tick
);

logic [31:0] counter_max;
logic [31:0] counter;

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
