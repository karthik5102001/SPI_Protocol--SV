`include "SPI_MASTER.sv"
//`include "SPI_SLAVE.sv" 

module top(clock,new_data,reset,din,dout,done);

input clock,new_data,reset;
input [11:0] din;
output [11:0] dout;
output done;

wire sync_clock,CS,MOSI;

SPI_MASTER M1 (clock,reset,new_data,din,sync_clock,CS,MOSI);
SPI_SLAVE S1 (sync_clock,CS,MOSI,dout,done);


endmodule