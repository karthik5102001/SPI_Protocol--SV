module SPI_SLAVE(sync_clock,CS,MOSI,dout,done);

input sync_clock,CS,MOSI;
output [11:0] dout;
output reg done;

int count = 0;

typedef  enum bit {start_on = 1'b0 , read_on = 1'b1} start_state;
   start_state state = start_on;

reg [11:0] temp = 0;

always @(posedge sync_clock) 
  begin
    case(state)
        start_on : begin                                  ////START STATE
                    done <= 1'b0;
                    if(CS == 1'b0)                         ////CHECKING FOR CS SIGNAL
                       begin
                       count <= 0;
                       state <= read_on;                  ////IF CS IS ACTIVE THEN MOVE TO READ STATE
                       temp <= 0;
                       end
                    else 
                       state <= start_on;                      ////IF CS IS NOT ACTIVE THEN STAY IN START STATE
                     $display("count value is %0d",count);                     
                    end   
         
         read_on : begin
                   if(count <= 11)
                       begin
                         // $display("Count = %0d",count);
                          temp <= {MOSI, temp[11:1]};       ////RIGHT SHIFT OPERATION  
                           count <= count + 1;              ////INCREMENTING COUNT      
                        end
                   else begin
                           count <= 0;
                           done <= 1'b1;
                           state<= start_on;                  ////IF COUNT REACHES 12 THEN MOVE TO START STATE
                         end
                    end
        endcase
     end

assign dout = temp;                                        ////OUTPUT DATA

   
  ////////////////////////////////////////--ASSERTIONS--//////////////////////////////////////////////
  
  property start_on_check;
    @(posedge sync_clock) (state == start_on) |=> if (CS == 0)
                                                       (count == 0) && (state == read_on) && (temp == 0)
                                                   else 
                                                        state == start_on;
  endproperty
  
  STATE_START : assert property (start_on_check);
    
   property read_on_check;
     @(posedge sync_clock) (state == read_on) |=> if ($past(count) <= 11)
                                                          count == $past(count) + 1 
                                                   else 
                                                     (count == 0) && (done == 1) && (state == start_on);
  endproperty
  
    STATE_READ : assert property (read_on_check);
    
    ////////////////////////////////////////--END--ASSERTIONS--//////////////////////////////////////////////

       
endmodule

