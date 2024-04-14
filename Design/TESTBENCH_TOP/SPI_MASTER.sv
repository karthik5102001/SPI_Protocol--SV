// Code your design here
////////////////////////////////////////--RTL--////////////////////////////////////////////////

module SPI_MASTER(clock,reset,new_data,din,sync_clock,CS,MOSI);
  input clock,new_data,reset;
  input [11:0] din;
  output reg sync_clock,CS,MOSI;
  
  typedef enum bit [1:0] {idel = 2'b00, enable = 2'b01, send = 2'b10, comp = 2'b11} start;
  start state = idel;
  
  int count = 0;
  int countclk = 0;
  
  reg [11:0] temp;
  
  
  always@(posedge clock)
    begin
      if(reset == 1'b1)
        begin 
          countclk = 32'd0;
          sync_clock = 1'b0;
        end
      else begin
        if(countclk < 10)
          countclk <= countclk +1;              ////--[CLOCK DIVIDER] WAIT TILL THE COUNT CLOCK REACHES
                                                //// 10 SO SYNC_CLK CAN BECOME INVERTED--////
        else 
          begin 
            countclk <= 0;
            sync_clock <= ~sync_clock;          /////ONE CLOCK OF SYNC_CLOCK IS EQUAL TO 10 CLOCK OF MAIN CLOCK--////
          end
      end
    end

  always@(posedge sync_clock)
    begin
      
      if(reset == 1'b1)
        begin
          CS <= 1'b1;
          MOSI <= 1'b0;
        end
      
      else 
        begin 
        
        case (state)
          idel : 
            begin 
            if(new_data == 1'b1)              ////--WAIT FOR NEW DATA TO ARRIVE--////
              begin
                temp <= din;                  ////--STORE THE DATA IN TEMP--////
                state = send;                 ////--CHANGE THE STATE TO SEND--////
                CS = 1'b0;                    ////--CS GOES LOW--////
                count = 0;
              end
            else 
              begin
                state = idel;                 ////--IF NO NEW DATA THEN IDLE--////
               temp = 11'd0;                  ////--RESET THE TEMP--////  
               end
            end
          
          
          send : 
            begin
              if(count < 11)                   ////--SEND THE DATA TO MOSI--////
              begin
               MOSI <= temp[count];            ////--SEND THE DATA TO MOSI BY LSB OF TEMP 1,2,4,...--////
               count = count + 1;
              end
            else 
              begin
                count = 32'd0;                 ////--RESET THE COUNT--////
                state = idel;                  ////--CHANGE THE STATE TO IDLE--////
                CS = 1'b1; 
                MOSI = 1'b0; 
              end
            end
          
        default : state = idel;  
        endcase
       end
    end 
  
  ////////////////////////////////////////--ASSERTIONS--//////////////////////////////////////////////
  
  property reset_main_clk;
    @(posedge clock) (reset |-> countclk == 0) and (reset |=> sync_clock == 0);
  endproperty
  
  RESET : assert property (reset_main_clk);// $display("RESET_MAIN WORKED"); else $display("RESET_MAIN FAILED");
      
    
  property reset_sclk;
    @(posedge sync_clock) reset |=> (CS) && (~MOSI) && (count == 0);
  endproperty
                                     
 RESET_SCLK : assert property (reset_sclk);// $display("RESET_SCLK WORKED"); else $display("RESET_SCLK FAILED"); 
    
      
  property sync_clk;
    @(posedge clock) disable iff(reset) ((countclk == 10) |=>  (countclk == 0) && (sync_clock == $past(sync_clock) + 1) ) or ((countclk < 10) |=> (countclk == $past(countclk) + 1)); 
  endproperty

   SYNC_CLOCK_CHECK :  assert property (sync_clk);// $display(SCLK and COUNTCLK WORKED"); else $display("SCLK and COUNTCLK FAILED"); 

  property idel_check;  
    @(posedge sync_clock) disable iff(reset) (state == idel) |=> if(new_data)                                                                  
                                                                    (state == send) && (temp == din) && (CS == 1'b0)                                                                    
                                                                  else                                                                     
                                                                    (state == idel) && (temp == 0) && (CS == 1'b1);                                                                       
  endproperty
  IDEL_CHECK :  assert property (idel_check); // $display("IDEL_CHECK WORKED"); else $display("IDEL_CHECK FAILED");   

 ///////////////////////////////////////--END-ASSERTION--//////////////////////////////////////////////

 endmodule
    
 //////////////////////////////////////////--END-RTL--//////////////////////////////////////////////////                                                                                                                                                                                                                                                    
  /*

 //////////////////////////////////////////--TESTBENCH--////////////////////////////////////////////////      
 module tb;
  reg clock,new_data,reset;
  reg [11:0] din;
  wire sync_clock,CS,MOSI;
      
   SPI_MASTER dut (clock,reset,new_data,din,sync_clock,CS,MOSI);
  
   initial begin
     clock = 1'b0;
     
     while(1) #1 clock = ~clock;
   end
   
   task reset_call;
     reset = 1;
     #5;
     reset = 0;
   endtask
   
   task new_data_call;
     new_data = 1'b1;
   //  @(negedge clock);
     din = $urandom_range(1,15);
   endtask
   
   
   initial begin
     reset_call;
     new_data_call;
     #500;
     new_data_call;
     #500;
     new_data_call;
     #500;
     new_data_call;
     #500;
     new_data_call;
     #500;
      new_data_call;
     #500;
     new_data_call;
     #500;
     new_data_call;
     #500;
     new_data_call;
     #500;
     new_data_call;
     #500;
     new_data_call;
     #500;
      new_data_call;
     #500;
     $finish;
   end
     initial 
       begin
         $dumpfile("dut.vcd");
        $dumpvars();     
        end

initial   $monitor("Sclk = %0b, CS = %0b, MOSI = %0b",sync_clock,CS,MOSI);
   
      endmodule 

////////////////////////////////////////--END-TESTBENCH--//////////////////////////////////////////////      
*/
