# SPI Protocol

Serial peripheral interface (SPI) is one of the most widely used interfaces between microcontroller and peripheral ICs such as sensors, ADCs, DACs, shift registers, SRAM, and others.

## Abstract
This repository has managed by writing System Verilog based testbench architecture for SPI Protocol, for further exploring on verification concept's, let's build another verification environment buy another framework like UVM, cocotb, e(Specman Elite) etc... .

In the Design we have more focused on MOSI way of communication for single Slave only and the design of SPI protocol is also influenced by it.

## Overview on SPI Protocol

- One Master and One Slave (upto 4 wires between them)
- CS (Chip Select) : Chip Select will choose which Slave want's to connect to which Master, when CS **low** we Transmit the data.
- Sync_clock : Sync_clock is a internal clock which runs in between Master and Slave only to make successful transaction of data with proper synchronization.
- MOSI (Master Out Slave In) : Data is transmitted by Master.
- MISO (Master In Slave Out) : Data recived by Master.

![SPI](https://www.circuitbasics.com/wp-content/uploads/2016/01/Introduction-to-SPI-Master-and-Slave.png)

![SPI_Communication](https://upload.wikimedia.org/wikipedia/commons/thumb/c/c8/SPI_basic_operation%2C_single_Main_%26_Sub.svg/552px-SPI_basic_operation%2C_single_Main_%26_Sub.svg.png)

## Documentation

- [Introduction to SPI Interface](http://www.analog.com/media/en/analog-dialogue/volume-52/number-3/introduction-to-spi-interface.pdf)

- [Supporting Links - 1](https://www.circuitbasics.com/basics-of-the-spi-communication-protocol/#google_vignette)

- [Supporting Links - 2](https://en.wikipedia.org/wiki/Serial_Peripheral_Interface)

- [Supporting Links - 3](https://www.ijariit.com/manuscripts/v6i4/V6I4-1312.pdf)

##  Open Source Software's
 **EDA Playground**:
 EDA Playground gives engineers immediate hands-on exposure to simulating and synthesizing SystemVerilog, Verilog, VHDL, C++/SystemC, and other HDLs. All you need is a web browser.


## Acknowledgements

 - [ EDA Playground web application ](https://www.edaplayground.com/)

![EDA Playground](https://www.doulos.com/media/2000/edaplaygroundready2.png)
