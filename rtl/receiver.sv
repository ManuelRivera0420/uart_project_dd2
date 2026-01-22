`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Manuel Enrique Rivera Acosta
// 
// Create Date: 10/28/2025 11:54:10 AM
// Design Name: 
// Module Name: receiver
//////////////////////////////////////////////////////////////////////////////////

// UART Receiver module
// - Oversampling x16
// - 1 start bit, 8 data bits, 1 stop bit
// - LSB first reception

module receiver #(parameter BYTE_WIDTH = 8)(
input logic clk,
input logic arst_n,     // Asynchronous active-low reset
input logic tick,       // Baud rate tick (baud x16)
input logic rx,         // Serial input line
output logic rx_done,   // Asserted when a full byte is received
output logic [BYTE_WIDTH - 1 : 0] data_out // Received parallel data
);

// Number of ticks per bit (x16 oversampling)
localparam BIT_SAMPLING     = 15;
localparam HALFBIT_SAMPLING = 7;

// Bit counter for received data bits
logic [4:0] nbits, nbits_next;

// Oversampling counter (counts ticks within a bit period)
logic [4:0] oversampling_count, oversampling_count_next;

// Register to store received data
logic [BYTE_WIDTH - 1 : 0] data_out_reg, data_out_reg_next;

// Next-state rx_done signal
logic rx_done_next;

// Receiver FSM states
typedef enum logic [2:0] {
    IDLE  = 3'b000, // Waiting for start bit
    START = 3'b001, // Start bit validation
    DATA  = 3'b010, // Data bit reception
    STOP  = 3'b011  // Stop bit check
} state_type;

state_type state_reg, state_next;

// Sequential logic: register updates
always_ff @(posedge clk or negedge arst_n) begin
    if(!arst_n) begin
        state_reg <= IDLE;
    end else begin
        oversampling_count <= oversampling_count_next;
        state_reg          <= state_next;
        nbits              <= nbits_next;
        data_out_reg       <= data_out_reg_next;
        rx_done            <= rx_done_next;
    end
end

// Combinational logic: FSM and next-state logic
always_comb begin
    // Default assignments
    oversampling_count_next = oversampling_count;
    nbits_next              = nbits;
    data_out_reg_next       = data_out_reg;
    state_next              = state_reg;
    rx_done_next            = rx_done;

    case(state_reg)

        // Wait for start bit (rx goes low)
        IDLE: begin
            rx_done_next            = 1'b0;
            oversampling_count_next = '0;
            data_out_reg_next       = '0;
            nbits_next              = '0;
            if (!rx) begin
                state_next = START;
            end
        end

        // Validate start bit by sampling at mid-bit
        START: begin
            if (tick) begin
                if (oversampling_count == BIT_SAMPLING) begin
                    oversampling_count_next = '0;
                    nbits_next              = '0;
                    data_out_reg_next       = '0;
                    state_next              = DATA;
                end else begin
                    oversampling_count_next = oversampling_count + 1'b1;
                    // Check start bit stability at half-bit
                    if (oversampling_count == HALFBIT_SAMPLING) begin
                        state_next = (!rx) ? START : IDLE;
                    end
                end
            end
        end

        // Receive data bits, LSB first
        DATA: begin
            if (tick) begin
                if (oversampling_count == BIT_SAMPLING) begin
                    oversampling_count_next = '0;
                    if (nbits == (BYTE_WIDTH - 1'b1)) begin
                        state_next = STOP;
                    end else begin
                        nbits_next = nbits + 1'b1;
                    end
                end else begin
                    oversampling_count_next = oversampling_count + 1'b1;
                    // Sample data at mid-bit
                    if (oversampling_count == HALFBIT_SAMPLING) begin
                        data_out_reg_next = {rx, data_out_reg[BYTE_WIDTH-1:1]};
                    end
                end
            end
        end

        // Check stop bit and finish reception
        STOP: begin
            if (tick) begin
                if (rx) begin
                    if (oversampling_count == BIT_SAMPLING) begin
                        rx_done_next            = 1'b1;
                        state_next              = IDLE;
                        oversampling_count_next = '0;
                    end else begin
                        oversampling_count_next = oversampling_count + 1'b1;
                    end
                end else begin
                    // Invalid stop bit, discard frame
                    state_next              = IDLE;
                    oversampling_count_next = '0;
                end
            end
        end

        default: begin
            state_next = state_reg;
        end
    endcase
end

// Output assignment
assign data_out = data_out_reg;

endmodule
