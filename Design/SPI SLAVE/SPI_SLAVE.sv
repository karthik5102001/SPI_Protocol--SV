module SPI_SLAVE(sync_clock,CS,MOSI,dout,done);

input sync_clock,CS,MOSI;
output [11:0] dout;
output reg done;

int count;

typedef  enum bit {start_on = 1'b0 , read_on = 1'b1} start_state;
   start_state state = start_on;

reg [11:0] temp;

always @(posedge sync_clock) 
  begin
    case(state)
        start_on : begin
                    done <= 1'b0;
                    if(CS == 1'b0)
                       state <= read_on;
                    else 
                       state <= start_on;                       
                    end   
         
         read_on : begin
                   if(count)
                       begin
                          count = count + 1;
                          temp = {MOSI,temp[11:0]};       ////RIGHT SHIFT OPERATION                   
                        end
                   else begin
                           count <= 0;
                           done <= 1'b1;
                           state<= start_on;
                         end
                    end
        endcase
     end

assign dout = temp;

endmodule

