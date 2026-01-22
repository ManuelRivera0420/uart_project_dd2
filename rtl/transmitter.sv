`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Manuel Enrique Rivera Acosta
// 
// Create Date: 10/28/2025 12:38:11 PM
// Design Name: 
// Module Name: transmitter
//////////////////////////////////////////////////////////////////////////////////

// UART Transmitter module
// - Oversampling x16
// - 1 start bit, 8 data bits, 1 stop bit
// - LSB first transmission

module transmitter #(parameter BYTE_WIDTH = 8)(
    input logic clk,        // System clock
    input logic arst_n,      // Asynchronous active-low reset
    input logic [BYTE_WIDTH - 1 : 0] data_in, // Parallel data byte to transmit
    input logic tick,       // Baud rate tick (baud x16)
    input logic tx_start,   // Starts transmission when asserted
    output logic tx,        // Serial output line
    output logic tx_done    // Asserted when transmission completes
);

// Number of ticks per bit (x16 oversampling)
localparam BIT_SAMPLING = 15;

// Shift register holding the data being transmitted
logic [BYTE_WIDTH - 1 : 0] shifted_data;
logic [BYTE_WIDTH - 1 : 0] shifted_data_next;

// Counter for transmitted data bits
logic [4:0] nbits;
logic [4:0] nbits_next;

// Oversampling counter (counts ticks within a bit)
logic [4:0] oversampling_count;
logic [4:0] oversampling_count_next;

// Next-state signals
logic tx_done_next;
logic tx_next;

// Transmitter FSM states
typedef enum logic [2:0]  {
    IDLE  = 3'b000, // Line idle, waiting for tx_start
    START = 3'b001, // Transmitting start bit
    DATA  = 3'b010, // Transmitting data bits
    STOP  = 3'b011  // Transmitting stop bit
} state_type;

state_type state_reg, state_next;

// Sequential logic: register updates
always_ff @(posedge clk or negedge arst_n) begin
    if(!arst_n) begin
        state_reg <= IDLE;
    end else begin
        state_reg          <= state_next;
        nbits              <= nbits_next;
        oversampling_count <= oversampling_count_next;
        shifted_data       <= shifted_data_next;
        tx_done            <= tx_done_next;
        tx                 <= tx_next;
    end
end

// Combinational logic: FSM behavior
always_comb begin
    // Default assignments
    state_next              = state_reg;
    nbits_next              = nbits;
    oversampling_count_next = oversampling_count;
    shifted_data_next       = shifted_data;
    tx_done_next            = tx_done;
    tx_next                 = tx;
	
    case(state_reg)
	
        // Idle state: line held high
        IDLE: begin
            tx_done_next            = 1'b0;
            nbits_next              = '0;
            tx_next                 = 1'b1;
            oversampling_count_next = '0;
            if(tx_start) begin 
                shifted_data_next = data_in; // Load data to shift register
                tx_next           = 1'b0;     // Start bit
                state_next        = START;
            end
        end
		
        // Start bit transmission
        START: begin
            if(tick) begin
                if(oversampling_count == BIT_SAMPLING) begin
                    oversampling_count_next = '0;
                    state_next              = DATA;
                end else begin
                    oversampling_count_next = oversampling_count + 1;
                end
            end
        end
		
        // Transmit data bits (LSB first)
        DATA: begin
            tx_next = shifted_data[0]; // Drive current data bit
            if(tick) begin
                if(oversampling_count == BIT_SAMPLING) begin
                    shifted_data_next       = {1'b0, shifted_data[7:1]}; // Shift right
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
		
        // Stop bit transmission
        STOP: begin
            tx_next = 1'b1; // Stop bit is logic high
            if(tick) begin
                if(oversampling_count == BIT_SAMPLING) begin
                    state_next   = IDLE;
                    tx_done_next = 1'b1;
                end else begin
                    oversampling_count_next = oversampling_count + 1;
                    state_next              = STOP;
                end
            end
        end

        default: begin
            state_next = state_reg;
        end		
    endcase
end

endmodule
