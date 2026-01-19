module uart_top_tb;

localparam BYTE_WIDTH = 8;

bit clk;
bit arst_n;
logic [BYTE_WIDTH - 1 : 0] data_in;
logic tx_start;
logic tx_done;
logic rx_done;
logic [BYTE_WIDTH - 1 : 0] data_out;

always #5ns clk = ~clk;
assign #50ns arst_n = 1'b1;

initial begin
    data_in = '0;
    tx_start = 1'b0;
    repeat (10) begin
        std::randomize(data_in);
        #1ms;
        @(posedge clk);
        tx_start = 1'b1;
        @(posedge clk);
        tx_start = 1'b0;
        @(posedge clk);
        #1ms;
    end    
end

initial begin
    #20ms;
    $finish;
end

logic [7:0] data_in_temp;

always_ff @(posedge clk or negedge arst_n) begin
  if (!arst_n)
    data_in_temp <= '0;
  else if (tx_start)
    data_in_temp <= data_in;
end


uart_top uart_top_i(
.clk(clk),
.arst_n(arst_n),
.data_in(data_in),
.tx_start(tx_start),
.tx_done(tx_done),
.rx_done(rx_done),
.data_out(data_out)
);

assert property(
    @(posedge clk)
    disable iff(!arst_n)
    rx_done |-> (data_out == data_in_temp)
);

assert property (
  @(posedge clk) 
  disable iff(!arst_n)
  $rose(tx_start) |-> ##[100000:115000] ($rose(tx_done) && (data_out == data_in_temp))
);

assert property (
  @(posedge clk) 
  disable iff(!arst_n)
  $rose(tx_start) |=>  (~uart_top_i.transmitter_i.tx)
);

endmodule
