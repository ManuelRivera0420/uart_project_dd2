module display_7_segments #(parameter DATA_WIDTH = 32)(
    input logic [DATA_WIDTH - 1 : 0] data_in,
    output logic [((DATA_WIDTH / 4) * 7) - 1 : 0] display
);

localparam ITERATIONS = DATA_WIDTH / 4;

function automatic [6:0] hex_nibbles (input [3:0] nibble);
    case (nibble)
        4'h0: return 7'b0000001; // 0
        4'h1: return 7'b1001111; // 1
        4'h2: return 7'b0010010; // 2
        4'h3: return 7'b0000110; // 3
        4'h4: return 7'b1001100; // 4
        4'h5: return 7'b0100100; // 5
        4'h6: return 7'b0100000; // 6
        4'h7: return 7'b0001111; // 7
        4'h8: return 7'b0000000; // 8
        4'h9: return 7'b0000100; // 9
        4'hA: return 7'b0001000; // A
        4'hB: return 7'b1100000; // b
        4'hC: return 7'b0110001; // C
        4'hD: return 7'b1000010; // d
        4'hE: return 7'b0110000; // E
        4'hF: return 7'b0111000; // F
        default: return 7'b1111111; // nothing
    endcase
endfunction

genvar i;
generate
    for(i = 0; i < ITERATIONS; i++) begin : gen_hex
        assign display[((i + 1) * 7) - 1 : i * 7] =
               hex_nibbles(data_in[((i + 1) * 4) - 1 : i * 4]);
    end
endgenerate


endmodule 