`timescale 1ns / 1ps

module tb();
 
reg clk = 0, rst = 0, newd = 0;
reg [11:0] din = 0;
wire [11:0] dout;
wire done;
 
always #10 clk = ~clk;
 
top dut (clk, newd, rst, din, dout, done);         ////INSTANTIATING THE DUT
  
 task reset;
rst = 1;
repeat(5) @(posedge clk);                         ////WAIT FOR 5 CLOCK CYCLES
rst = 0;
  endtask
  
  
  task run;
newd = 1;
    din = $urandom_range(1,1000);              ////RANDOM DATA
@(posedge dut.S1.sync_clock);                  ////WAIT FOR SYNC CLOCK
newd = 0;  
@(posedge done);  
  endtask
  
  
initial begin
  reset;                                        ////RESET
  run;                                          ////RUN
  @(posedge dut.S1.sync_clock); 
  run;
  @(posedge dut.S1.sync_clock);
  run;
  @(posedge dut.S1.sync_clock);
  run;
  @(posedge dut.S1.sync_clock);
  run;
   @(posedge dut.S1.sync_clock);
  run;
  @(posedge dut.S1.sync_clock);
  run;
  
$finish;
end
  
  initial 
       begin
         $dumpfile("dut.vcd");
        $dumpvars();     
        end
 
 
endmodule