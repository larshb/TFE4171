library ieee;
use ieee.std_logic_1164.all;

entity atm is
 port(
  clk       : in  std_ulogic;
  error_i   : in  std_ulogic;
  multiple_i: in  std_ulogic;
  correct_o : out std_ulogic;
  dismiss_o : out std_ulogic
 );
end atm;

architecture rtl of atm is
 signal state_s: std_ulogic;
begin
 process
 begin
  wait until clk'event and clk = '1';
  state_s <= error_i;
 end process;
 correct_o <= not state_s and error_i and not multiple_i;
 dismiss_o <= (state_s and error_i) or (error_i and multiple_i);
end rtl;
