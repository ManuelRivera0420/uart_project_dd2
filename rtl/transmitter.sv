`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Manuel Enrique Rivera Acosta
// 
// Create Date: 10/28/2025 12:38:11 PM
// Design Name: 
// Module Name: transmitter
// Project Name: 
//////////////////////////////////////////////////////////////////////////////////


module transmitter #(parameter BYTE_WIDTH = 8)(
    input logic clk, // clock signal
    input logic arst_n, // asynchronous reset
    input logic [BYTE_WIDTH - 1 : 0] data_in, // DATA_IN TO BE SENT TO THE RECEIVER MODULE BIT BY BIT THROUGH THE TX
    input logic tick, // TICK COMING FROM THE BAUD RATE GENERATOR
    input logic tx_start, // TX_START SIGNAL TO BEGIN THE BYTE TRANSMISSION
    output logic tx, // SERIAL OUTPUT BIT TO TRANSMIT INTO THE RECEIVER RX INPUT SIGNAL
    output logic tx_done // DONE SIGNAL INDICATING THAT THE BYTE HAS BEEN SENT
);

localparam BIT_SAMPLING = 15; // localparam for the oversampling counter of the uart x16

logic [BYTE_WIDTH - 1 : 0] shifted_data; // temporal register to store the data shifted to the tx
logic [BYTE_WIDTH - 1 : 0] shifted_data_next; // next-state temporal register shifted_data

logic [4:0] nbits; // variable to count the number of bits that has been sent
logic [4:0] nbits_next; // next-state nbits variable

logic [4:0] oversampling_count; // oversampling counter for the uart x16
logic [4:0] oversampling_count_next; // next-state oversampling counter

logic tx_done_next; // next-state tx_done signal (transmission done signal)
logic tx_next;  // next-state tx signal (serial output bit)

typedef enum logic [2:0]  {IDLE = 3'b000, START = 3'b001, DATA = 3'b010, STOP = 3'b011} state_type;

state_type state_reg, state_next;

always_ff @(posedge clk or negedge arst_n) begin
    if(!arst_n) begin
        state_reg <= IDLE;
    end else begin
        state_reg <= state_next;
        nbits <= nbits_next;
        oversampling_count <= oversampling_count_next;
        shifted_data <= shifted_data_next;
        tx_done <= tx_done_next;
	tx <= tx_next;
    end
end

always_comb begin
	state_next = state_reg;
	nbits_next = nbits;
	oversampling_count_next = oversampling_count;
	shifted_data_next = shifted_data;
	tx_done_next = tx_done;
	tx_next = tx;
	
    case(state_reg)
	
        IDLE: begin
            tx_done_next = 1'b0;
            nbits_next = '0;
            tx_next = 1'b1;
            oversampling_count_next = '0;
            if(tx_start) begin 
                shifted_data_next = data_in;
                tx_next = 1'b0;
                state_next = START;
            end
        end
		
        START: begin
            if(tick) begin
                if(oversampling_count == BIT_SAMPLING) begin
                    oversampling_count_next = '0;
                    state_next = DATA;             
                end else begin
                    oversampling_count_next = oversampling_count + 1;
                end
            end
        end
		
        DATA: begin
            tx_next = shifted_data[0];
            if(tick) begin
                if(oversampling_count == BIT_SAMPLING) begin
                    shifted_data_next = {1'b0, shifted_data[7:1]};
                    oversampling_count_next = '0;
                    if(nbits == BYTE_WIDTH - 1) begin
                        state_next = STOP;
                    end else begin
                        nbits_next = nbits + 1'b1;
                    end
                end else begin
                    oversampling_count_next = oversampling_count + 1;
                end
            end
        end
		
        STOP: begin
            tx_next = 1'b1;
            if(tick) begin
                if(oversampling_count == BIT_SAMPLING) begin
                    state_next = IDLE;
                    tx_done_next = 1'b1;
                end else begin
                    oversampling_count_next = oversampling_count + 1;
                    state_next = STOP;
                end
            end
        end
	default: begin
		state_next = state_reg;
	end		
    endcase
end

endmodule
