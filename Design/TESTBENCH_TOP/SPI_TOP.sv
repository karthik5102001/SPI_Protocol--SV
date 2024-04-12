

module top(clock,new_data,reset,din,dout,done);

input clock,new_data,reset;
input [11:0] din;
output [11:0] dout;
output done;

wire sync_clock,CS,MOSI;                            ////DECLARING WIRES FOR SPI MASTER MODULE

SPI_MASTER M1 (clock,reset,new_data,din,sync_clock,CS,MOSI);  ////INSTANTIATING SPI MASTER MODULE
SPI_SLAVE S1 (sync_clock,CS,MOSI,dout,done);                  ////INSTANTIATING SPI SLAVE MODULE


endmodule