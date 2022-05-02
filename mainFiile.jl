


function main()
include("typechecker.jl")

typechecker.t

end

main()



using Pluto
using PlutoUI

with_terminal

Pluto.run()



# IN THE NOTEBOOK:

# Go to the sample PlutoUI nb for lots of fun widgets!
using Pluto
using PlutoUI
having_fun ? md"🎈🎈" : md"☕"
@bind having_fun CheckBox(default=true)
tt = "Hello Julia From Terminalll";

# Method 1: Using PlutoUI: with_terminal()
with_terminal() do
    println(tt)
end
# This is bc println(tt) will NOT show, it shows in the REal terminal!✔
# Method 1: Using PlutoUI: with_terminal()

message
@bind message TextField((30,7); default="Hello")
using PlutoUI



i = [1]

adder(msg) = (i[1]+=1; msg*msg)
begin message; i[1];  end # message is to TRIGGER the reevaluation of the cell !!!
adder(message)
@bind message TextField((30,7); default="Hello")
using PlutoUI
