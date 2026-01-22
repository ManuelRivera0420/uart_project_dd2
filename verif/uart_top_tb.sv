module uart_top_tb;

localparam BYTE_WIDTH = 8;

bit clk;
bit arst_n;

uart_interface intf(clk, arst_n);

always #5ns clk = ~clk;
assign #50ns arst_n = 1'b1;

logic [BYTE_WIDTH - 1 : 0] rand_data;
initial begin
	repeat(100) begin
		std::randomize(rand_data);
		intf.write_data_in(rand_data);
		#1200us;
	end
end

initial begin
    #20ms;
    $finish;
end

localparam BAUD_CNT_CYCLES = ((100_000_000) / (9600 * 16));
logic [7:0] data_in_temp;
logic [31:0] baud_counter_tb;
logic tb_tick;

always_ff @(posedge clk or negedge arst_n) begin
	if(!arst_n) begin
		tb_tick <= 1'b0;
		baud_counter_tb <= '0;
	end else if (baud_counter_tb == BAUD_CNT_CYCLES) begin
		tb_tick <= 1'b1;
		baud_counter_tb <= baud_counter_tb <= '0;
	end else begin
		tb_tick <= 1'b0;
		baud_counter_tb <= baud_counter_tb + 1'b1;
	end
end

always_ff @(posedge clk or negedge arst_n) begin
  if (!arst_n)
    data_in_temp <= '0;
  else if (intf.tx_start)
    data_in_temp <= intf.data_in;
end


uart_top uart_top_i(
.clk(clk),
.arst_n(arst_n),
.data_in(intf.data_in),
.tx_start(intf.tx_start),
.tx_done(intf.tx_done),
.rx_done(intf.rx_done),
.data_out(intf.data_out)
);

assert property(
    @(posedge clk)
    disable iff(!arst_n)
   intf.rx_done |-> (intf.data_out == data_in_temp)
);

// to check //
assert property (
  @(posedge clk) 
  disable iff(!arst_n)
  $rose(intf.tx_start) |-> ##[100000:115000] ($rose(intf.tx_done) && (intf.data_out == data_in_temp))
);

assert property (
  @(posedge clk) 
  disable iff(!arst_n)
  $rose(intf.tx_start) |=>  (~uart_top_i.transmitter_i.tx)
);

initial begin
    $shm_open("shm_db");
    $shm_probe("ASMTR");
end

endmodule
