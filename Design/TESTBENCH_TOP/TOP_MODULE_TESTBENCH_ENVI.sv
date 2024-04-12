////////////////////--INTERFACE--///////////////////////

interface SPI_if ;
  logic reset;
  logic new_data;
   logic clock;
  logic [11:0] din;
  logic [11:0] dout;
   logic done;
   logic sync_clock;
endinterface

///////////////////--TRACSACTION--///////////////////////

class transcation;
   bit new_data;
  rand bit [11:0] din;
  bit [11:0] dout;
  
  constraint DATAIN {din inside{[0:2047]};}
  
  function void display(string str);
    $display("[%0s] : DATAIN = %0d | DATAOUT = %0d",str,din,dout);
  endfunction
  
  
  function transcation copy();                ////--DEEP COPY FUNCTION--/////
    copy = new();
    copy.new_data = this.new_data;
    copy.din = this.din;
    copy.dout = this.dout;
  endfunction  
  
endclass

//////////////////////--GENERATOR--//////////////////////


class generator;
  
  transcation tr;
  mailbox #(transcation) gen_driv;
  event trig_driver;
  event trig_scrb;
  event done;
  int count;
  
  function new(mailbox #(transcation) gen_driv);
    this.gen_driv = gen_driv;
    tr = new();
  endfunction
  
  virtual task run();
    repeat(count)
      begin
    assert(tr.randomize) else $display("RANDOMIZE FAILED");
    gen_driv.put(tr);
        $display("[GEN] : DATA GENERATED FROM GENERATOR ");
        tr.display("GEN");
      //  @(trig_driver);                                  //->DRIVER TRIGGER
        @(trig_scrb);                                    //->SCRIBBLE TRIGGER
      end
    -> done;                                              //->DONE TRIGGER
    endtask
 
endclass

/////////////////////--DRIVER--////////////////////////

class driver;
  transcation tr_1, copy_tr_1;
  virtual SPI_if spi_drive;
  mailbox #(transcation) gen_driv;
  mailbox #(bit [11:0] ) driv_scrb;
  
  event trig_driver;

  function new(mailbox #(transcation) gen_driv, mailbox #(bit [11:0] ) driv_scrb, virtual SPI_if spi_drive);
    this.spi_drive = spi_drive;
    this.gen_driv = gen_driv;
    this.driv_scrb = driv_scrb;
    tr_1 = new();
  endfunction
  
  task reset();
     spi_drive.new_data <= 0;
     spi_drive.reset <= 1;                              ////--RESET FUNCTION--////
     spi_drive.din <= 0;
    
    repeat(10) @(posedge spi_drive.clock);
      spi_drive.reset <= 0; 
    repeat(5) @(posedge spi_drive.clock);
    $display("RESET DONE");
   endtask
  
  
  
  virtual task run();
    forever
      begin
        
        gen_driv.get(tr_1); 
        
        tr_1.display("DRIV");
        
    //    copy_tr_1 = tr_1.copy;               ////--DEEP COPY FUNCTION--////              
        spi_drive.new_data <= 1; 
        
        spi_drive.din <= tr_1.din; 
         
        driv_scrb.put(tr_1.din);
        
        @(posedge spi_drive.sync_clock);
        spi_drive.new_data <= 0;                  ////Many assertion will fail here if we explictly make new_data low 
                                                  ////because it will not be able to match the assertion condition
                                                  ////we have to make it low after sync_clock or else the data in will
                                                  ////not be able to match the data out as new_data will be high all the time.
        @(posedge spi_drive.done);
        
        
        $display("[DRIV] : DATA DRIVEN TO DUV ");
       
        @(posedge spi_drive.sync_clock);
        
        // -> trig_driver;                             //->DRIVER TRIGGER TO GENERATOR
      end
  endtask
  
endclass

/////////////////////--MONITOR--////////////////////////

class monitor;
  
  transcation tr_2;
  virtual SPI_if spi_drive;
  mailbox #(bit [11:0]) moni_scrb;
  int data;
  bit [11:0] data_in;
  
  function new( mailbox #(bit [11:0]) moni_scrb, virtual SPI_if spi_drive);
    this.moni_scrb = moni_scrb;
    this.spi_drive = spi_drive;
  endfunction
  
  virtual task run();
    tr_2 = new();
    forever
      begin      
        @(posedge spi_drive.sync_clock);

        @(posedge spi_drive.done);                  ////--WAIT FOR DONE SIGNAL--////
        
        tr_2.dout = spi_drive.dout;
        
          @(posedge spi_drive.sync_clock);
        
        tr_2.display("MONI");

        
        $display("[MONI] : DATA RECIVED FROM DUV = %0d",tr_2.dout);    
        
        moni_scrb.put(tr_2.dout);

      end
 
  endtask
     
  endclass
        
/////////////////////--SCOREBOARD--////////////////////////

class scoreboard;
  
  transcation tr_3;
  
  bit [11:0] drive_data;
  bit [11:0] monitor_data;
  
  int q1[$];
  int q2[$];
  
  event trig_scrb;
  
  int data_success;
  int data_failed;
 
  mailbox #(bit [11:0]) moni_scrb;
  mailbox #(bit [11:0] ) driv_scrb;
  
  
  function new(mailbox #(bit [11:0]) moni_scrb, mailbox #(bit [11:0] ) driv_scrb);
   
    this.moni_scrb = moni_scrb;
    this.driv_scrb = driv_scrb;
    tr_3 = new();
  endfunction
  
  virtual task run();
    forever begin
      driv_scrb.get(drive_data);                       ////--GET DATA FROM DRIVER--////
         q1.push_back(drive_data);                     ////--PUSH DATA TO QUEUE_1--////
      
      moni_scrb.get(monitor_data);                     ////--GET DATA FROM MONITOR--////
         q2.push_back(monitor_data);                   ////--PUSH DATA TO QUEUE_2--////
      $display("[SCRB] : DRIVER DATA = %0d | MONITOR DATA = %0d",drive_data,monitor_data);
      if(drive_data == monitor_data)
        begin
          $display("[SCRB] : DATA MATCHED");
          $display("++++++++++++++++++++++++++++++++++++");
          data_success ++;
        end
      else begin
        $display("DATA MISSMATCH");
         $display("++++++++++++++++++++++++++++++++++++");
        data_failed ++;
      end 
      -> trig_scrb;
    end
  endtask
  
 virtual task REPORT(); 
   $display("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    $display("[SCRB] : DATA MATCH = %0d", data_success); 
    $display("[SCRB] : DATA MISS_MATCH = %0d",data_failed);  
    $display("[SCRB] : DATA FROM MONITOR = %0p",q2);
    $display("[SCRB] : DATA FROM DRIVER = %0p",q1);    
    $display("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");  
  endtask
  
  
endclass
        
/////////////////////--ENVIORNMENT--////////////////////////
        
class enviornment;
  
  generator gen;
  driver driv;
  monitor moni;
  scoreboard scrb;
  
   
  event trig_scrb;
  event trig_driver;
  event done;
  
  
  virtual SPI_if spi_drive;  
  
  mailbox #(transcation) gen_driv;
  mailbox #(bit [11:0] ) driv_scrb;
  mailbox #(bit [11:0]) moni_scrb;

  function new (  virtual SPI_if spi_drive );
    moni_scrb = new();
    gen_driv = new();
    driv_scrb =new();
    
    this.spi_drive = spi_drive;
    gen = new(gen_driv);
    driv = new(gen_driv,driv_scrb,spi_drive);
    moni = new(moni_scrb,spi_drive);
    scrb = new(moni_scrb, driv_scrb);
 
    //gen.trig_scrb =  trig_scrb;
    scrb.trig_scrb = gen.trig_scrb;                  //->SCORE BOARD TRIGGER
   // gen.trig_driver =  trig_driver;
    driv.trig_driver = gen.trig_driver;              //->DRIVER TRIGGER
    this.done = gen.done;
  endfunction
  
  task pre_clear;
    driv.reset();
  endtask
  
  task run();
    fork 
      gen.run();
      driv.run();
      moni.run();
      scrb.run();
    join_none
  endtask
  
  task post_test;
    wait(done.triggered);
    scrb.REPORT();
    $finish;
  endtask
  
  virtual task run_env();
    pre_clear();
    run();
    post_test();
  endtask
  
  endclass
        
/////////////////////--TOP-MODULE--////////////////////////
     
        
module top;
  
  int data = 11;
  int count = 15;
  
  
  SPI_if spi_drive();
  
  TOP_SPI DUV (spi_drive.clock, spi_drive.new_data, spi_drive.reset, spi_drive.din,spi_drive.dout,spi_drive.done);
  
  enviornment envi;
  
  initial 
    begin
      spi_drive.clock <= 0;
    end
  
  always #5  spi_drive.clock <= ~spi_drive.clock;         ////--CLOCK GENERATION--////
    
  assign spi_drive.sync_clock = DUV.M1.sync_clock;        ////--ASSIGNING SYNC CLOCK--////
  
  initial begin
     envi = new(spi_drive);
    envi.gen.count = count;
     envi.moni.data = data; 
    $display("START");
    envi.run_env();
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
  
endmodule