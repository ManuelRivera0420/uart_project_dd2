`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Manuel Enrique Rivera Acosta
// 
// Create Date: 10/28/2025 11:54:10 AM
// Design Name: 
// Module Name: receiver
//////////////////////////////////////////////////////////////////////////////////

module receiver #(parameter BYTE_WIDTH = 8)(
input logic clk,
input logic arst_n,
input logic tick, // TICK COMING FROM THE BAUD RATE GENERATOR
input logic rx, // INPUT SERIAL COMING FROM THE TRANSMITTER TX
output logic rx_done, // DONE SIGNAL TO INDICATE THAT THE BYTE HAS BEEN RECEIVED
output logic [BYTE_WIDTH - 1 : 0] data_out // OUPUT SIGNAL FOR THE BYTE RECEIVED
);

localparam BIT_SAMPLING = 15;
localparam HALFBIT_SAMPLING = 7;

logic [4:0] nbits;
logic [4:0] nbits_next;
logic [4:0] oversampling_count;
logic [4:0] oversampling_count_next;
logic [BYTE_WIDTH - 1 : 0] data_out_reg;
logic [BYTE_WIDTH - 1 : 0] data_out_reg_next;
logic rx_done_next;

typedef enum logic [2:0] {IDLE = 3'b000, START = 3'b001, DATA = 3'b010, STOP = 3'b011} state_type;

state_type state_reg, state_next;

always_ff @(posedge clk or negedge arst_n) begin
    if(!arst_n) begin
        state_reg <= IDLE;
    end else begin
        oversampling_count <= oversampling_count_next;
        state_reg <= state_next;
        nbits <= nbits_next;
        data_out_reg <= data_out_reg_next;
        rx_done <= rx_done_next;
    end
end

always_comb begin
    oversampling_count_next = oversampling_count;
    nbits_next              = nbits;
    data_out_reg_next       = data_out_reg;
    state_next              = state_reg;
    rx_done_next = 1'b0;

    case(state_reg)
        IDLE: begin
            rx_done_next = 1'b0;
            oversampling_count_next = '0;
            data_out_reg_next       = data_out_reg;
            nbits_next              = '0;
            if (!rx) begin
                data_out_reg_next = '0;
                state_next = START;
			end
        end

        START: begin
            if (tick) begin
                if (oversampling_count == BIT_SAMPLING) begin
                    oversampling_count_next = '0;
                    nbits_next = '0;
                    data_out_reg_next = '0;
                    state_next = DATA;
                end else begin
                    oversampling_count_next = oversampling_count + 1'b1;
                    if (oversampling_count == HALFBIT_SAMPLING) begin
                        state_next = (!rx) ? START : IDLE;
					end	
                end
            end
        end

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
                    if (oversampling_count == HALFBIT_SAMPLING) begin
                        data_out_reg_next = {rx, data_out_reg[BYTE_WIDTH-1:1]};
					end
                end
            end
        end

        STOP: begin
            if (tick) begin
                if (rx) begin
                    if (oversampling_count == BIT_SAMPLING) begin
                        state_next = IDLE;
                        oversampling_count_next = '0;
                    end else begin
                        oversampling_count_next = oversampling_count + 1'b1;
						if (oversampling_count == HALFBIT_SAMPLING) begin
							rx_done_next = 1'b1;
						end
                    end
                end else begin
                    state_next = IDLE;
                    oversampling_count_next = '0;
                end
            end
        end
		
    endcase
end

assign data_out = data_out_reg;

endmodule