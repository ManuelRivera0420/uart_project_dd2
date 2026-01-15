`timescale 1ns / 1ps
module instruction_memory #(
    parameter BYTE_WIDTH = 8,       // Ancho de cajón de la memoria (1 Byte)
    parameter MEM_DEPTH  = 1024,    // Número de renglones de memoria
    parameter ADDR_WIDTH = 10,      // con 10 bits podemos direccionar 1024 renglones
    parameter DATA_WIDTH = 32       // Ancho de instrucción (32 bits)
)
(
    input  logic                   clk,
    
    // Puerto de Lectura (PC)
    input  logic [ADDR_WIDTH-1:0]  rd_addr,   // Dirección de lectura (PC)
    output logic [DATA_WIDTH-1:0]  rd_data,   // Instrucción que sale
    
    // Puerto de escritura (FIFO)
    input  logic [DATA_WIDTH-1:0]  data_in,   // Dato (instrucción) que viene de la FIFO
    input  logic [ADDR_WIDTH-1:0]  wr_addr,   // Dirección (10 bits para 1024 espacios)
    input  logic                   w_en       // Write Enable
);

    localparam BANK_DEPTH = MEM_DEPTH / 4; // 256 renglones por banco

    // bank3 = byte [31:24] (MSB), bank0 = byte [7:0] (LSB)
    logic [BYTE_WIDTH-1:0] bank0 [0:BANK_DEPTH-1]; 
    logic [BYTE_WIDTH-1:0] bank1 [0:BANK_DEPTH-1]; 
    logic [BYTE_WIDTH-1:0] bank2 [0:BANK_DEPTH-1]; 
    logic [BYTE_WIDTH-1:0] bank3 [0:BANK_DEPTH-1]; 

    // 1. Inicialización (Limpieza + programa)
    initial begin : init_memory
        // Limpia toda la memoria
        for (int i = 0; i < BANK_DEPTH; i++) begin
            bank0[i] = {BYTE_WIDTH{1'b0}};
            bank1[i] = {BYTE_WIDTH{1'b0}};
            bank2[i] = {BYTE_WIDTH{1'b0}};
            bank3[i] = {BYTE_WIDTH{1'b0}};
        end
    end

    // 2. Escritura paralela en los 4 bancos
    // [ADDR_WIDTH-1:2] para elegir el renglón dentro del banco (PC alineado a 4 bytes)
    always_ff @(posedge clk) begin
        if (w_en) begin
            bank3[wr_addr[ADDR_WIDTH-1:2]] <= data_in[31:24]; // MSB
            bank2[wr_addr[ADDR_WIDTH-1:2]] <= data_in[23:16];
            bank1[wr_addr[ADDR_WIDTH-1:2]] <= data_in[15:8];
            bank0[wr_addr[ADDR_WIDTH-1:2]] <= data_in[7:0];   // LSB
        end
    end

    // 3. Lectura (Combinacional)
    assign rd_data = {
        bank3[rd_addr[ADDR_WIDTH-1:2]],
        bank2[rd_addr[ADDR_WIDTH-1:2]],
        bank1[rd_addr[ADDR_WIDTH-1:2]],
        bank0[rd_addr[ADDR_WIDTH-1:2]]
    };

endmodule
