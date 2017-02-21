-------------------------------------------------------------------------------
-- Title      :  HDLC core
-- Project    :  HDLC Standalone controller with buffers
-------------------------------------------------------------------------------
-- File        : hdlc.vhd
-- Author      : Jamil Khatib  (khatib@ieee.org)
-- Organization: OpenCores Project
-- Created     :2001/03/022
-- Last update: 2001/03/22
-- Platform    : 
-- Simulators  : Modelsim 5.3XE/Windows98,NC-SIM/Linux
-- Synthesizers: 
-- Target      : 
-- Dependency  : ieee.std_logic_1164
--               hdlc.hdlc_components_pkg
-------------------------------------------------------------------------------
-- Description:  HDLC controller
-------------------------------------------------------------------------------
-- Copyright (c) 2000 Jamil Khatib
-- 
-- This VHDL design file is an open design; you can redistribute it and/or
-- modify it and/or implement it after contacting the author
-- You can check the draft license at
-- http://www.opencores.org/OIPC/license.shtml
 
-------------------------------------------------------------------------------
-- Revisions  :
-- Revision Number :   1
-- Version         :   0.1
-- Date            :   22 March 2001
-- Modifier        :   Jamil Khatib (khatib@ieee.org)
-- Desccription    :   Created
-- ToOptimize      :
-- Bugs            :   
-------------------------------------------------------------------------------
-- $Log: not supported by cvs2svn $
-- Revision 1.3  2001/04/22 20:08:16  jamil
-- Top level simulation
--
-- Revision 1.1  2001/03/22 21:58:01  jamil
-- Initial release
--
-------------------------------------------------------------------------------
LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
 
LIBRARY work;
USE work.hdlc_components_pkg.ALL;
 
ENTITY hdlc_ent IS
  GENERIC (
    FCS_TYPE  :     INTEGER := 2;       -- FCS 16
    ADD_WIDTH :     INTEGER := 7);      -- Internal buffer address width
  PORT (
    rst       : IN  STD_LOGIC;          -- Peripheral Reset
    clk       : IN  STD_LOGIC;          -- Peripheral Clock

    TxClk     : IN  STD_LOGIC;          -- Tx serial Clock
    RxClk     : IN  STD_LOGIC;          -- Rx serial Clock
    Tx        : OUT STD_LOGIC;          -- Tx serial line
    Rx        : IN  STD_LOGIC;          -- Rx serial line
    TxEN      : IN  STD_LOGIC;          -- Tx serial Enable
    RxEn      : IN  STD_LOGIC;          -- Rx serial Enable

    RxD	      : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);  -- Rx Data
    TxD	      : IN STD_LOGIC_VECTOR(7 DOWNTO 0);  -- Tx Data

    RxD_Rd_Buff	: IN  STD_LOGIC;     	-- Rx Read Data Buffer
    TxD_Wr_Buff : IN  std_logic;      	-- Tx Write Data Buffer
    TxD_EN      : IN  STD_LOGIC;        -- Tx Data Enable (Write Frame Completed)
    TxD_AF	: IN  std_logic;    	-- Tx Aborted Frame
   
    TxD_fin	: OUT std_logic;        -- Tx Transmission Done (Read Frame completed)
    RxD_OF    	: OUT STD_LOGIC;        -- Rx Data Buffer Overflow
    TxD_Full	: OUT std_logic;        -- Tx Buffer Full (no more write is allowed)

    RxD_Fr_ln 	: OUT STD_LOGIC_VECTOR(ADD_WIDTH-1 DOWNTO 0); -- Rx Data Frame Length
    RxD_Rdy   	: OUT STD_LOGIC;        -- Rx Data Ready
    TxD_AT	: OUT std_logic;    	-- Tx Aborted Transmission
    RxD_FE	: OUT STD_LOGIC;     	-- Rx Frame Error
    RxD_FCSE	: OUT STD_LOGIC;        -- Rx FCS error
    RxD_AS	: OUT STD_LOGIC);       -- Rx Abort signal
 
END hdlc_ent;
 
ARCHITECTURE hdlc_str OF hdlc_ent IS
  SIGNAL rst_n : STD_LOGIC;             -- Internal Reset
 
  SIGNAL Tx_rdy_D1          : STD_LOGIC;  -- Tx rdy signal (Domain 1)
  SIGNAL Tx_rdy_D2          : STD_LOGIC;  -- Tx rdy signal (Domain 2)
  SIGNAL Tx_ack             : STD_LOGIC;  -- Tx Acknowledge signal
  SIGNAL TXD_D1             : STD_LOGIC_VECTOR(7 DOWNTO 0);  -- Tx Data bus (Domain 1)
  SIGNAL TXD_D2             : STD_LOGIC_VECTOR(7 DOWNTO 0);  -- Tx Data Bus (Domain 2)
  SIGNAL Tx_ValidFrame_D1   : STD_LOGIC;  -- Tx Valid Frame (Domain 1)
  SIGNAL Tx_ValidFrame_D2   : STD_LOGIC;  -- Tx Valid Frame (Domain 2)
  SIGNAL Tx_AbortedTrans_D1 : STD_LOGIC;  -- Tx Aborted Transmission (Domain 1)
  SIGNAL Tx_AbortedTrans_D2 : STD_LOGIC;  -- Tx Aborted Transmission (Domain 2)
  SIGNAL Tx_AbortFrame_D1   : STD_LOGIC;  -- Tx Abort Frame (Domain 1)
  SIGNAL Tx_AbortFrame_D2   : STD_LOGIC;  -- Tx Abort Frame (Domain 2)
  SIGNAL Tx_WriteByte_D1    : STD_LOGIC;  -- Tx Write bytes (Domain 1)
  SIGNAL Tx_WriteByte_D2    : STD_LOGIC;  -- Tx Write Byte (Domain 2)
 
  SIGNAL Rx_ValidFrame_D1 : STD_LOGIC;  -- Rx Valid Frame (Domain1)
  SIGNAL Rx_ValidFrame_D2 : STD_LOGIC;  --  Rx Valid Frame (Domain 2)
 
  SIGNAL RxD_D1 : STD_LOGIC_VECTOR(7 DOWNTO 0);  -- Rx Data bus (Domain 1)
  SIGNAL RXD_D2 : STD_LOGIC_VECTOR(7 DOWNTO 0);  -- Rx data bus (Domain 2)
 
  SIGNAL Rx_FrameError_D1 : STD_LOGIC;  -- Rx Frame Error (Domain 1)
  SIGNAL Rx_FrameError_D2 : STD_LOGIC;  -- Rx Frame Error (Domain 2)
 
  SIGNAL Rx_AbortSignal_D1 : STD_LOGIC;  -- Rx Abort signal (Domain 1)
  SIGNAL Rx_AbortSignal_D2 : STD_LOGIC;  -- Rx Abort signal (Domain 2)
 
  SIGNAL Rx_Readbyte_D1 : STD_LOGIC;    -- Rx Read Byte (Domain 1)
  SIGNAL Rx_Readbyte_D2 : STD_LOGIC;    -- Rx Read Byte (Domain 2)
 
  SIGNAL Rx_rdy_D1 : STD_LOGIC;         -- Rx rdy (Domain 1)
  SIGNAL Rx_rdy_D2 : STD_LOGIC;         -- Rx rdy (Domain 2)
 
 
  SIGNAL TxDataAvail   : STD_LOGIC;     -- Tx Data Available from the Buffer
  SIGNAL Tx_RdBuff     : STD_LOGIC;     -- Tx Read Byte from the buffer
  SIGNAL TxDone        : STD_LOGIC;     -- TxDone bit (Interrupt)
  SIGNAL TxEnable      : STD_LOGIC;     -- TxEnable Bit
  SIGNAL Tx_Full       : STD_LOGIC;     -- Tx Full Buffer Bit
  SIGNAL TxDataInBuff  : STD_LOGIC_VECTOR(7 DOWNTO 0);
                                        -- Tx input data to buffer
  SIGNAL TxDataOutBuff : STD_LOGIC_VECTOR(7 DOWNTO 0);  -- Tx Data output from buffer
  SIGNAL Tx_Wr_Buff    : STD_LOGIC;     -- Write to Tx Buffer
 
  SIGNAL FCSen : STD_LOGIC;             -- FCS Enable (both Tx & Rx)
 
  SIGNAL Rx_WrBuff        : STD_LOGIC;  -- Write to Rx Buffer
  SIGNAL Rx_EOF           : STD_LOGIC;  -- RX End Of Frame
  SIGNAL Rx_FrameSize     : STD_LOGIC_VECTOR(ADD_WIDTH-1 DOWNTO 0);
                                        -- Rx Frame size
  SIGNAL Rx_DataBuff      : STD_LOGIC_VECTOR(7 DOWNTO 0);  -- Rx Input data buffer
  SIGNAL Rx_Buff_Overflow : STD_LOGIC;  -- Rx Buffer overflow
  SIGNAL Rx_FCSerr        : STD_LOGIC;  -- Rx FCS error
  SIGNAL RxDataBuffOut    : STD_LOGIC_VECTOR(7 DOWNTO 0);  --  Rx Data BUFFER output
 
  SIGNAL Rx_Rd_Buff : STD_LOGIC;        -- Rx Read Data Buffer
  SIGNAL RxRdy_int  : STD_LOGIC;        -- Rx Ready interrupt
  signal CLK_I 	    : STD_LOGIC;
  signal RxRdy      : STD_LOGIC;
  signal RxOverflow : std_logic;
 
BEGIN  -- hdlc_str
 
  rst_n 	<= NOT rst;
  CLK_I 	<= clk;
  TxEnable      <= TxD_EN;
  Rx_FrameSize  <= RxD_Fr_ln; 
  RxRdy         <= RxD_Rdy;
  RxDataBuffOut <= RxD;
  RxOverflow    <= RxD_OF;
  Rx_Rd_Buff	<= RxD_Rd_Buff;
  TxDone        <= TxD_fin;
  Tx_Full     	<= TxD_Full;
  TxDataInBuff  <= TxD;
  Tx_Wr_Buff    <= TxD_Wr_Buff;
  FCSen         <= '1';
  Tx_AbortedTrans_D2     <= TxD_AT;
  Tx_AbortFrame_D2       <= TxD_AF;
  Rx_FrameError_D2	 <= RxD_FE; 
  Rx_FCSErr      <= RxD_FCSE;
  Rx_AbortSignal_D2       <= RxD_AS; 
 
  TxSynch : txSynch_ent
    PORT MAP (
      rst_n           => rst_n,
      clk_D1          => Txclk,
      clk_D2          => CLK_I,
      rdy_D1          => Tx_rdy_D1,
      rdy_D2          => Tx_rdy_D2,
      ack             => Tx_ack,
      TXD_D1          => TXD_D1,
      TXD_D2          => TXD_D2,
      ValidFrame_D1   => Tx_ValidFrame_D1,
      ValidFrame_D2   => Tx_ValidFrame_D2,
      AbortedTrans_D1 => Tx_AbortedTrans_D1,
      AbortedTrans_D2 => Tx_AbortedTrans_D2,
      AbortFrame_D1   => Tx_AbortFrame_D1,
      AbortFrame_D2   => Tx_AbortFrame_D2,
      WriteByte_D1    => Tx_WriteByte_D1,
      WriteByte_D2    => Tx_WriteByte_D2);
 
  TxBuff : TxBuff_ent
    GENERIC MAP (
      ADD_WIDTH     => ADD_WIDTH)
    PORT MAP (
      TxClk         => CLK_I,
      rst_n         => rst_n,
      RdBuff        => Tx_RdBuff,
      Wr            => Tx_Wr_Buff,
      TxDataAvail   => TxDataAvail,
      TxEnable      => TxEnable,
      TxDone        => TxDone,
      TxDataOutBuff => TxDataOutBuff,
      TxDataInBuff  => TxDataInBuff,
      Full          => Tx_Full);
 
  TxFCS : Txfcs_ent
    GENERIC MAP (
      FCS_TYPE    => FCS_TYPE)
    PORT MAP (
      TxClk       => CLK_I,
      rst_n       => rst_n,
      FCSen       => FCSen,
      ValidFrame  => Tx_ValidFrame_D2,
      WriteByte   => Tx_WriteByte_D2,
      rdy         => Tx_rdy_D2,
      ack         => Tx_ack,
      TxData      => TXD_D2,
      TxDataAvail => TxDataAvail,
      RdBuff      => Tx_RdBuff,
      TxDataBuff  => TxDataOutBuff);
 
 
  TxCore : TxChannel_ent
    PORT MAP (
      TxClk        => TxClk,
      rst_n        => rst_n,
      TXEN         => TXEN,
      Tx           => Tx,
      ValidFrame   => Tx_ValidFrame_D1,
      AbortFrame   => Tx_AbortFrame_D1,
      AbortedTrans => Tx_AbortedTrans_D1,
      WriteByte    => Tx_WriteByte_D1,
      rdy          => Tx_rdy_D1,
      TxData       => TxD_D1);
 
  RxChannel : RxChannel_ent
    PORT MAP (
      Rxclk       => Rxclk,
      rst         => rst_n,
      Rx          => Rx,
      RxData      => RxD_D1,
      ValidFrame  => Rx_ValidFrame_D1,
      FrameError  => Rx_FrameError_D1,
      AbortSignal => Rx_AbortSignal_D1,
      Readbyte    => Rx_Readbyte_D1,
      rdy         => Rx_rdy_D1,
      RxEn        => RxEn);
 
 
  RxSynch : RxSynch_ent
    PORT MAP (
      rst_n          => rst_n,
      clk_D1         => Rxclk,
      clk_D2         => CLK_I,
      rdy_D1         => Rx_rdy_D1,
      rdy_D2         => Rx_rdy_D2,
      RXD_D1         => RxD_D1,
      RXD_D2         => RXD_D2,
      ValidFrame_D1  => Rx_ValidFrame_D1,
      ValidFrame_D2  => Rx_ValidFrame_D2,
      AbortSignal_D1 => Rx_AbortSignal_D1,
      AbortSignal_D2 => Rx_AbortSignal_D2,
      FrameError_D1  => Rx_FrameError_D1,
      FrameError_D2  => Rx_FrameError_D2,
      ReadByte_D1    => Rx_ReadByte_D1,
      ReadByte_D2    => Rx_ReadByte_D2);
 
  RxBuff : RxBuff_ent
    GENERIC MAP (
      FCS_TYPE      => FCS_TYPE,
      ADD_WIDTH     => ADD_WIDTH)
    PORT MAP (
      Clk           => CLK_I,
      rst_n         => rst_n,
      DataBuff      => Rx_DataBuff,
      EOF           => Rx_EOF,
      WrBuff        => Rx_WrBuff,
      FrameSize     => Rx_FrameSize,
      RxRdy         => RxRdy_int,
      RxDataBuffOut => RxDataBuffOut,
      Overflow      => Rx_Buff_Overflow,
      Rd            => Rx_Rd_Buff);
 
 
  RxFCS : RxFCS_ent
    GENERIC MAP (
      FCS_TYPE   => FCS_TYPE)
    PORT MAP (
      clk        => CLK_I,
      rst_n      => rst_n,
      RxD        => RxD_D2,
      ValidFrame => Rx_ValidFrame_D2,
      rdy        => Rx_rdy_D2,
      Readbyte   => Rx_Readbyte_D2,
      DataBuff   => Rx_DataBuff,
      WrBuff     => Rx_WrBuff,
      EOF        => Rx_EOF,
      FCSen      => FCSen,
      FCSerr     => Rx_FCSerr);
 
 
END hdlc_str;
