
module Memory(
    input wire[7:0] address,
    input wire[7:0] data,
    input wire wr, //Read = 0, Write = 1
    input wire cs, //Chip is enable when cs = 0
    input wire clock,
    output reg[7:0] o // Output
);
    //Declaration o?f the RAM Area
    reg[7:0] RAM_DATA[0:255];
    //Read Ram data from the file
    initial $readmemh("RAM.mem", RAM_DATA);
    //Read the selected data from RAM
    always @(*) begin
        o = ~wr && ~cs ? RAM_DATA[address] : 8'hZ;
    end
    
    //Write the data to RAM
    always @(posedge clock) begin
        if (wr && ~cs) begin
            RAM_DATA[address] <= data; 
        end
    end
endmodule

//part_1
module n_bit_register #(parameter n = 8)(
    input Enable, 
    input CLK, 
    input [1:0] FunSel, 
    input [n-1:0] Input,
    output reg [n-1:0] Q
    );
    always@(posedge CLK) begin
        if (Enable) begin
            case (FunSel)
                2'b00: Q <= 0;
                2'b01: Q <= Input;
                2'b10: Q <= Q - 1;
                2'b11: Q <= Q + 1;
            endcase
        end
     end   
endmodule
 
//part 2a
module IR_register(
    input Enable,
    input CLK,
    input Signal,
    input [1:0] FunSel,
    input [7:0] Input,
    output [15:0] IROut
    );
    
    reg [15:0] IR;
    
    always@(*) begin
        if(Signal) 
        begin
            IR <= {Input, IROut[7:0]};
        end
        else 
        begin
            IR <= {IROut[15:8], Input};
        end    
    end
    
    n_bit_register #(16) q(Enable, CLK, FunSel, IR, IROut);  
    
endmodule

//part2b 
module RF_register(
    input [7:0] Input,
    input [2:0] O1Sel,
    input [2:0] O2Sel,
    input CLK,
    input [1:0] FunSel,
    input [3:0] RSel,
    input [3:0] TSel,
    output reg [7:0] O1,
    output reg [7:0] O2
    );
    
    wire [7:0] R1_out;
    wire [7:0] R2_out;
    wire [7:0] R3_out;
    wire [7:0] R4_out;
    wire [7:0] T1;
    wire [7:0] T2;
    wire [7:0] T3;
    wire [7:0] T4;

    n_bit_register #(8) q1(RSel[3], CLK, FunSel, Input, R1_out);  
    n_bit_register #(8) q2(RSel[2], CLK, FunSel, Input, R2_out);  
    n_bit_register #(8) q3(RSel[1], CLK, FunSel, Input, R3_out);  
    n_bit_register #(8) q4(RSel[0], CLK, FunSel, Input, R4_out);  

    n_bit_register #(8) q5(TSel[3], CLK, FunSel, Input, T1);  
    n_bit_register #(8) q6(TSel[2], CLK, FunSel, Input, T2);  
    n_bit_register #(8) q7(TSel[1], CLK, FunSel, Input, T3);  
    n_bit_register #(8) q8(TSel[0], CLK, FunSel, Input, T4);
    
    always@(*) begin
        case (O1Sel) 
            3'b000: O1 <= T1;
            3'b001: O1 <= T2;
            3'b010: O1 <= T3;
            3'b011: O1 <= T4;
            3'b100: O1 <= R1_out;
            3'b101: O1 <= R2_out;
            3'b110: O1 <= R3_out;
            3'b111: O1 <= R4_out;
        endcase
        
        case (O2Sel) 
            3'b000: O2 <= T1;
            3'b001: O2 <= T2;
            3'b010: O2 <= T3;
            3'b011: O2 <= T4;
            3'b100: O2 <= R1_out;
            3'b101: O2 <= R2_out;
            3'b110: O2 <= R3_out;
            3'b111: O2 <= R4_out;
        endcase
    end
endmodule

//part 2c
module ARF_register(
    input CLK,
    input [7:0] in,
    input [1:0] FunSel,
    input [1:0] OutASel,
    input [1:0] OutBSel,
    input [3:0] RSel,
    output reg [7:0] OutA,
    output reg [7:0] OutB
);
    wire [7:0] pc_out;
    wire [7:0] ar_out;
    wire [7:0] sp_out;
    wire [7:0] pcpast_out;
    n_bit_register #(8) PC(RSel[3],CLK,FunSel, in, pc_out);
    n_bit_register #(8) AR(RSel[2],CLK,FunSel, in, ar_out);
    n_bit_register #(8) SP(RSel[1],CLK,FunSel, in, sp_out);
    n_bit_register #(8) PCP(RSel[0],CLK,FunSel, in, pcpast_out);
    
    
    always@(*) begin
        case (OutASel)
            2'b00: OutA <= ar_out ;
            2'b01: OutA <= sp_out;
            2'b10: OutA <= pcpast_out;
            2'b11: OutA <= pc_out;
        endcase
        case (OutBSel)
            2'b00: OutB <= ar_out ;
            2'b01: OutB <= sp_out;
            2'b10: OutB <= pcpast_out;
            2'b11: OutB <= pc_out;
        endcase
    end
endmodule

module ALU(
    input CLK,
    input [7:0] A,
    input [7:0] B,
    input [3:0] FunSel,
    output reg [7:0] Out, 
    output reg [3:0] Flags 
    );
    reg [8:0] nine_temp;
    wire [8:0] A_nine;
    assign A_nine = {1'b0, A};
    wire [8:0] Bnot_nine;
    assign Bnot_nine = {1'b0, ~B};
    
    initial Flags = 4'b0000;
 
    always@(*) begin
        case (FunSel)
            4'b0000: Out <= A;
            4'b0001: Out <= B;
            4'b0010: Out <= ~A;
            4'b0011: Out <= ~B;
            4'b0100: //addition
                begin
                    nine_temp <= A + B;
                    Out <= nine_temp[7:0];
                end 
            4'b0101: //subtraction
                begin
                    nine_temp <= A_nine + Bnot_nine + 1;
                    Out <= nine_temp[7:0];
                end
            4'b0110: //comparison 
                begin //-2 ve -1 ile dene
                    if(A[7]!= B[7]) begin
                        Out <= (A[7] == 0) ? A : 8'b00000000;
                    end 
                    else begin
                        nine_temp <= A_nine + Bnot_nine + 1;
                        Out <= (nine_temp[8] == 1) ? A : 8'b00000000;
                    end
                end
            4'b0111: Out <= A & B;
            4'b1000: Out <= A | B;
            4'b1001: Out <= ~(A & B);
            4'b1010: Out <= A ^ B;
            4'b1011: Out <= A << 1; //lsl
            4'b1100: Out <= A >> 1; //lsr
            4'b1101: Out <= A <<< 1; //asl
            4'b1110: 
                begin
                    Out <= A >>> 1; // asr
                    Out[7] <= A[7];
                end
            4'b1111: Out <= {A[0], A[7:1]}; //csr
        endcase
            
    end
    
    always@(posedge CLK) begin

        case(FunSel)
            4'b0000: //zn
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b0001:  //zn
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b0010:  //zn
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b0011:  //zn
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b0100: //all
                begin
                    if((A[7] == B[7]) && (B[7] != Out[7])) Flags[0] = 1'b1; 
                    else Flags[0] = 1'b0;
                       
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    if(nine_temp[8] == 1) Flags[2] <= 1'b1;
                    else Flags[2] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b0101:  //all
                begin
                    if((A[7] == 0 && B[7] == 1 && Out[7] == 1) || (A[7] == 1 && B[7] == 0 && Out[7] == 0)) Flags[0] <= 1'b1;
                    else Flags[0] <= 1'b0;
                    
                    if(Out[7] == 1) Flags[1] <= 1'b1;  
                    else Flags[1] <= 1'b0;
                    
                    if(nine_temp[8] == 1) Flags[2] <= 1'b1;
                    else Flags[2] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b0110:  //all
                begin
                if((A[7] == 0 && B[7] == 1 && nine_temp[8] == 1) || (A[7] == 1 && B[7] == 0 && nine_temp[8] == 0)) Flags[0] <= 1'b1;
                else Flags[0] <= 1'b0;
            
                if(Out[7] == 1) Flags[1] <= 1'b1; 
                else Flags[1] <= 1'b0;
             
                if(nine_temp[8] == 1) Flags[2] <= 1'b1;
                else Flags[2] <= 1'b0;
            
                if(Out == 8'b0) Flags[3] <= 1'b1;
                else Flags[3] <= 1'b0;
            end
            4'b0111:  //zn
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b1000:  //zn
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b1001:  //zn
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b1010: //zn
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b1011: //zcn
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    Flags[2] = A[7];
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end 
            4'b1100: //zcn
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    Flags[2] = A[0];
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b1101: //zno
                begin
                    if(A[7] == A[6]) Flags[0] = 0;
                    else Flags[0] = 1;
                    
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end 
            4'b1110: //z
                begin
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end
            4'b1111: //zcn 
                begin
                    if(Out[7] == 1) Flags[1] <= 1'b1; 
                    else Flags[1] <= 1'b0;
                    
                    Flags[2] = A[0];
                    
                    if(Out == 8'b0) Flags[3] <= 1'b1;
                    else Flags[3] <= 1'b0;
                end     
        endcase
    end
endmodule

module ALU_System(
    input [2:0]RF_OutASel, 
    input [2:0]RF_OutBSel, 
    input [1:0]RF_FunSel, 
    input [3:0]RF_RSel, 
    input [3:0]RF_TSel,
    
    input [3:0]ALU_FunSel,
    
    input [1:0]ARF_OutCSel, //these inputs should be ARF_OutASel and ARF_OutBSel but they are written as ARF_OutCSel
    input [1:0]ARF_OutDSel, //and ARF_OutDSel at the testbench, thus we wrote them according to the testbench
    input [1:0]ARF_FunSel,
    input [3:0]ARF_RegSel,
    
    input      IR_LH,
    input      IR_Enable,
    input [1:0]IR_Funsel,
    
    input      Mem_WR,
    input      Mem_CS,
    
    input [1:0]MuxASel,
    input [1:0]MuxBSel,
    input      MuxCSel,
    
    input      Clock
    );
    
    reg [7:0]MuxAOut;
    reg [7:0]MuxBOut;
    reg [7:0]MuxCOut;
    
    wire [7:0]ALUOut;
    wire [3:0]ALUOutFlag; 
    
    wire [7:0]MemoryOut;
    
    wire [15:0]IROut;
    
    wire [7:0]ARF_AOut;
    wire [7:0]Address;
    
    wire [7:0]AOut; 
    wire [7:0]BOut; 
    

    
    always@(*) begin
        case(MuxASel)
            2'b00: MuxAOut <= ALUOut;
            2'b01: MuxAOut <= MemoryOut;
            2'b10: MuxAOut <= IROut[7:0];
            2'b11: MuxAOut <= ARF_AOut;
        endcase
        case(MuxBSel)
            2'b00: MuxBOut <= ALUOut;
            2'b01: MuxBOut <= MemoryOut;
            2'b10: MuxBOut <= IROut[7:0];
            2'b11: MuxBOut <= ARF_AOut;
        endcase
        case(MuxCSel)
            1'b0: MuxCOut <= AOut;
            1'b1: MuxCOut <= ARF_AOut;
        endcase        
    end
    
    IR_register ir(IR_Enable, Clock, IR_LH, IR_Funsel, MemoryOut, IROut);
    ARF_register arf(Clock, MuxBOut, ARF_FunSel, ARF_OutCSel, ARF_OutDSel, ARF_RegSel, ARF_AOut, Address);
    RF_register rf(MuxAOut, RF_OutASel, RF_OutBSel, Clock, RF_FunSel, RF_RSel, RF_TSel, AOut, BOut);
    ALU alu(Clock, MuxCOut, BOut, ALU_FunSel, ALUOut, ALUOutFlag);
    Memory mem(Address, ALUOut, Mem_WR, Mem_CS, Clock, MemoryOut);


endmodule

module CPUSystem(
    input Clock,
    output reset,
    output [2:0] T,
    output [7:0] R1,
    output [7:0] R2,
    output [7:0] R3,
    output [7:0] R4,
    output [7:0] PC,
    output [7:0] AR,
    output [7:0] SP,
    output [15:0] IR_Out
    );
     
    wire [3:0] ALU_OutFlag; 
    
    reg [3:0] ALU_FunSel;
     
    reg [1:0] ARF_OutASel; 
    reg [1:0] ARF_OutBSel; 
    reg [3:0] ARF_RSel;
    reg [1:0] ARF_FunSel;
    
    reg [1:0] MuxASel;
    reg [1:0] MuxBSel;
    reg MuxCSel; 
    
    reg [1:0] IR_FunSel;
    reg IR_LH;
    reg IR_Enable;
    
    reg wr;
    reg cs;
    
    reg [2:0] RF_Out1Sel;
    reg [2:0] RF_Out2Sel;
    reg [1:0] RF_FunSel;
    reg [3:0] RF_RSel; 
    reg [3:0] RF_TSel;
   
    reg operation;
    reg [2:0] t;
    
    wire [7:0]ARF_AOut;
    wire [7:0]RF_Out1;
    reg [7:0]MuxCOut;
    wire [7:0]RF_Out2;
    wire [7:0]ALUOut;
    reg [7:0]MuxAOut;
    reg [7:0]MuxBOut;
    wire [7:0]Address;
    wire [7:0]MemoryOut;
    
    ALU_System mySystem(RF_Out1Sel, RF_Out2Sel, RF_FunSel, RF_RSel, RF_TSel, ALU_FunSel, ARF_OutASel, ARF_OutBSel, 
                            ARF_FunSel, ARF_RSel, IR_LH, IR_Enable, IR_FunSel, wr, cs, MuxASel, MuxBSel, MuxCSel, Clock);
  
    assign ARF_AOut = mySystem.ARF_AOut;
    assign RF_Out1 = mySystem.AOut;
    assign RF_Out2 = mySystem.BOut;
    assign ALUOut = mySystem.ALUOut;
    assign Address = mySystem.Address;
    assign MemoryOut = mySystem.MemoryOut;  
    assign IR_Out = mySystem.IROut;
    assign ALU_OutFlag = mySystem.ALUOutFlag;               
                        
                        
    assign reset = ~operation;
    assign T = t;    
    
    initial operation = 0;
    
    always@(negedge Clock) begin
        if (operation == 0) begin
            operation <= 1;
        
            // Clear RF
            RF_FunSel <= 2'b00;
            RF_RSel <= 4'b1111;
            RF_TSel <= 4'b0000;
            
            // Clear ARF
            ARF_FunSel <= 2'b00;
            ARF_RSel <= 4'b1111;
            
            // Clear IR
            IR_FunSel <= 2'b00;
            IR_Enable <= 1;
            IR_LH <= 1;
            t <= 3'b000;
        end
        
         if(t == 3'b000) begin
            // Increment PC
             ARF_RSel <= 4'b1000;
             ARF_FunSel <= 2'b11;
             ARF_OutBSel <= 2'b11;
             
             cs <= 0;
             wr <= 0;
             // Load the LSB of IR from Memory
             IR_LH <= 0;
            IR_Enable <= 1'b1;
            IR_FunSel <= 2'b01;
            
            t <= t + 3'b001;
        end
    
        else if (t == 3'b001) begin
            // Load the MSB of IR from Memory
            IR_LH <= 1; 
             cs <= 0;
             wr <= 0;   // Read
             // Protect data in RF
             RF_RSel <= 4'b0000;
             t <= t + 3'b001;
            
            t <= t + 3'b001;
         end
         
         else if (t == 3'b010 | t == 3'b011)begin 
             IR_Enable <= 0;
             if(IR_Out[15:12] == 4'h0 | IR_Out[15:12] == 4'h1 | IR_Out[15:12] == 4'h2 | IR_Out[15:12] == 4'h3 | 
                IR_Out[15:12] == 4'h4 | IR_Out[15:12] == 4'hB) begin
                if(t == 3'b010) begin
                     MuxASel <= 2'b00;
                     MuxBSel <= 2'b00;
                     RF_FunSel <= 2'b01;
                     ARF_FunSel <= 2'b01;
                     
                     if(IR_Out[10] == 0) begin
                         case(IR_Out[9:8])
                             2'b00: RF_RSel <= 4'b1000;
                             2'b01: RF_RSel <= 4'b0100;
                             2'b10: RF_RSel <= 4'b0010;
                             2'b11: RF_RSel <= 4'b0001;                               
                         endcase
                         ARF_RSel <= 4'b0000;
                     end
                     
                     else if(IR_Out[10] == 1) begin
                         case(IR_Out[9:8])
                             2'b00: ARF_RSel <= 4'b0010;
                             2'b01: ARF_RSel <= 4'b0100;
                             2'b10: ARF_RSel <= 4'b1000;
                             2'b11: ARF_RSel <= 4'b1000;
                         endcase
                         RF_RSel <= 4'b0000;
                     end
                    case({IR_Out[6], IR_Out[2]})
                         2'b00: 
                         begin
                             RF_Out2Sel <= {1'b1, IR_Out[1:0]};
                             RF_Out1Sel <= {1'b1, IR_Out[5:4]};     
                             MuxCSel <= 1'b0;                      
                         end
                         2'b01:
                         begin
                             RF_Out2Sel <= {1'b1, IR_Out[5:4]}; 
                             case(IR_Out[1:0]) 
                                 2'b00: ARF_OutASel <= 2'b01;
                                 2'b01: ARF_OutASel <= 2'b00;
                                 2'b10: ARF_OutASel <= 2'b11;
                                 2'b11: ARF_OutASel <= 2'b01;
                             endcase
                             MuxCSel <= 1'b1;
                         end
                         2'b10:
                         begin
                             RF_Out2Sel <= {1'b1, IR_Out[1:0]}; 
                             case(IR_Out[5:4]) 
                                 2'b00: ARF_OutASel <= 2'b01;
                                 2'b01: ARF_OutASel <= 2'b00;
                                 2'b10: ARF_OutASel <= 2'b11;
                                 2'b11: ARF_OutASel <= 2'b01;
                             endcase
                             MuxCSel <= 1'b1;
                         end
                    endcase
                    case(IR_Out[15:12])
                         4'h0: ALU_FunSel <= 4'b0111; //AND +
                         4'h1: ALU_FunSel <= 4'b1000; //OR + 
                         4'h2:                        //NOT+
                         begin 
                             if(IR_Out[6] == 1) ALU_FunSel <= 4'b0010;
                             else ALU_FunSel <= 4'b0011;
                         end 
                         4'h3: ALU_FunSel <= 4'b0100; //ADD +
                         4'h4: ALU_FunSel <= 4'b0101; //SUB +
                         4'hB:                        //MOV + 
                         begin
                             if(IR_Out[6] == 1) ALU_FunSel <= 4'b0000;
                             else ALU_FunSel <= 4'b0001; 
                         end
                     endcase
                     t <= 3'b000;
                 end
             end
         
             else if(IR_Out[15:12] == 4'h5 | IR_Out[15:12] == 4'h6) begin //LSR LSL
                 if(T == 3'b010) begin
                 MuxASel <= 2'b00;
                 MuxBSel <= 2'b00;
                 RF_FunSel <= 2'b01;
                 ARF_FunSel <= 2'b01;
                 if(IR_Out[10] == 0) begin
                     case(IR_Out[9:8])
                         2'b00: RF_RSel <= 4'b1000;
                         2'b01: RF_RSel <= 4'b0100;
                         2'b10: RF_RSel <= 4'b0010;
                         2'b11: RF_RSel <= 4'b0001;                               
                     endcase
                     ARF_RSel <= 4'b0000;
                 end
                 else if(IR_Out[10] == 1) begin
                     case(IR_Out[9:8])
                         2'b00: ARF_RSel <= 4'b0010;
                         2'b01: ARF_RSel <= 4'b0100;
                         2'b10: ARF_RSel <= 4'b1000;
                         2'b11: ARF_RSel <= 4'b1000;
                     endcase
                     RF_RSel <= 4'b0000;
                 end
                 if(IR_Out[6] == 0) begin
                     MuxCSel <= 1'b0;
                     RF_Out1Sel <= {1'b1, IR_Out[5:4]};
                 end
                 else if(IR_Out[6] == 1) begin
                     MuxCSel <= 1'b1;
                     case(IR_Out[5:4]) 
                         2'b00: ARF_OutASel <= 2'b01;
                         2'b01: ARF_OutASel <= 2'b00;
                         2'b10: ARF_OutASel <= 2'b11;
                         2'b11: ARF_OutASel <= 2'b01;
                     endcase
                 end
                 case(IR_Out[15:12])
                     4'h5: ALU_FunSel <= 4'b1011; //LSR
                     4'h6: ALU_FunSel <= 4'b1100; //LSL
                 endcase
                 t <= 3'b000;
                 end
             end
                                     
                                     
             else if(IR_Out[15:12] == 4'h7 | IR_Out[15:12] == 4'h8) begin //INC DEC
                 if(t == 3'b010) begin
                     ALU_FunSel <= 4'b0000;
                     if(IR_Out[6] == 1) begin
                         case(IR_Out[5:4]) 
                             2'b00: ARF_OutASel <= 2'b01;
                             2'b01: ARF_OutASel <= 2'b00;
                             2'b10: ARF_OutASel <= 2'b11;
                             2'b11: ARF_OutASel <= 2'b01;
                         endcase
                         case(IR_Out[5:4])
                             2'b00: ARF_RSel <= 4'b0010;
                             2'b01: ARF_RSel <= 4'b0100;
                             2'b10: ARF_RSel <= 4'b1000;
                             2'b11: ARF_RSel <= 4'b1000;
                         endcase
                         case(IR_Out[15:12])
                             4'h7: ARF_FunSel <= 2'b11;
                             4'h8: ARF_FunSel <= 2'b10;                            
                         endcase
                         MuxCSel <= 1'b1;
                     end
                     else if (IR_Out[6] == 0) begin
                         RF_Out1Sel <= {1'b1, IR_Out[5:4]};
                         case(IR_Out[5:4])
                             2'b00: RF_RSel <= 4'b1000;
                             2'b01: RF_RSel <= 4'b0100;
                             2'b10: RF_RSel <= 4'b0010;
                             2'b11: RF_RSel <= 4'b0001;                               
                         endcase     
                         case(IR_Out[15:12])
                             4'h7: RF_FunSel <= 2'b11;
                             4'h8: RF_FunSel <= 2'b10;                            
                         endcase   
                         MuxCSel <= 1'b0;            
                     end
                     t <= t + 3'b001;
                 end
                 if(t == 3'b011) begin
                     if(IR_Out[10] == 0) begin
                         MuxASel <= 2'b00;
                         RF_FunSel <= 2'b01;
                         case(IR_Out[9:8])
                             2'b00: RF_RSel <= 4'b1000;
                             2'b01: RF_RSel <= 4'b0100;
                             2'b10: RF_RSel <= 4'b0010;
                             2'b11: RF_RSel <= 4'b0001;                               
                         endcase
                         ARF_RSel <= 4'b0000;
                     end
                     else if(IR_Out[10] == 1) begin
                         MuxBSel <= 2'b00;
                         ARF_FunSel <= 2'b01;
                         case(IR_Out[9:8])
                             2'b00: ARF_RSel <= 4'b0010;
                             2'b01: ARF_RSel <= 4'b0100;
                             2'b10: ARF_RSel <= 4'b1000;
                             2'b11: ARF_RSel <= 4'b1000;
                         endcase
                         RF_RSel <= 4'b0000;
                     end
                     t <= 3'b000;
                 end
             end
             else if( IR_Out[15:12]==4'h9) // BRA
                 if(T == 3'b010) begin
                 begin
                     MuxBSel <= 2'b10;
                     ARF_FunSel <= 2'b01;
                     ARF_RSel <= 4'b1000;
                     
                     t <= 3'b000;
                 end 
                 end
             
             else if( IR_Out[15:12]==4'hA) // BNE
                 if(t == 3'b010) begin
                 begin
                     if(ALU_OutFlag[3] == 0)
                     begin
                         MuxBSel <= 2'b10;
                         ARF_FunSel <= 2'b01;
                         ARF_RSel <= 4'b1000;
                     end
                     else 
                         ARF_RSel <= 4'b0000;
                     t <= 3'b000;
                  end
                end
             
             else if( IR_Out[15:12]==4'hC) begin //LD
                  if(t == 3'b010) begin
                    
                    if (IR_Out[10] == 0) begin    // (IM)
                    
                         MuxASel <= 2'b10;
                         RF_FunSel <= 2'b01;
                         RF_Out1Sel <= 3'b100;
                         case(IR_Out[9:8])
                             2'b00: RF_RSel <= 4'b1000;
                             2'b01: RF_RSel <= 4'b0100;
                             2'b10: RF_RSel <= 4'b0010;
                             2'b11: RF_RSel <= 4'b0001;
                         endcase
                         ARF_RSel <= 4'b0000;
                         t <= 3'b000;
                     end
                 else begin      // (D) 
                     ARF_OutBSel <= 2'b00;
                     cs <= 0;
                     wr <= 0;
                     MuxASel <= 2'b01;
                     RF_FunSel <= 2'b01;
                     case(IR_Out[9:8])
                         2'b00: ARF_RSel <= 4'b0010;
                         2'b01: ARF_RSel <= 4'b0100;
                         2'b10: ARF_RSel <= 4'b1000;
                         2'b11: ARF_RSel <= 4'b1000;
                     endcase
                     ARF_RSel <= 4'b0000;
                     t <= 3'b000;
                 end
                 
                 end
             end
            
             else if( IR_Out[15:12]==4'hD)  begin//M[AR] <- Rx  
                 if(t == 3'b100) begin
                     ARF_OutBSel <= 2'b00; //AR'yi se?erek address memorye g?nderildi
                     wr <=1; //Write
                     cs <= 0;
                     RF_RSel <= 4'b0000; //protect data
                     RF_Out2Sel <= {1'b1, IR_Out[9:8]}; //select Rx
                     ALU_FunSel <= 4'b0001; //B will be transfered directly
                     ARF_RSel <= 4'b0000; //protect data in ARF
                     t <= 3'b000;
                 end
             end
                 
             else if( IR_Out[15:12]==4'hE) begin  //PUL: SP<-SP+1, RX<-M[SP]
                 if(t == 3'b100) begin
                     ARF_FunSel <= 2'b11; //increment SP
                     ARF_RSel <= 4'b1000; //enable SP
                     ARF_OutBSel <= 2'b01; //B output SP
                     wr <=0; //read
                     cs <=0;
                     MuxASel <= 2'b01; //memory out transferred to RF
                     case(IR_Out[9:8]) //enable relative Rx
                         2'b00: RF_RSel <= 4'b1000;
                         2'b01: RF_RSel <= 4'b0100;
                         2'b10: RF_RSel <= 4'b0010;
                         2'b11: RF_RSel <= 4'b0001;
                     endcase
                     RF_FunSel <= 2'b01; //Load
                     t <= 3'b000;
                 end
             end
                 
             else if( IR_Out[15:12]==4'hF) begin //PSH M[SP]<- Rx, SP <-SP-1
     
                 if(t == 3'b100) begin
                     RF_RSel <=4'b0000; 
                     ARF_OutBSel <= 2'b01; //SP send to memory as address
                     wr <= 1; //write
                     cs <=0;
                     RF_Out2Sel <= {1'b1, IR_Out[9:8]}; //select Rx to output B
                     ALU_FunSel <= 4'b0001; //B will be transfered directly
                     ARF_RSel <=4'b0010; //enable SP
                     ARF_FunSel <= 2'b10; //decrement SP
                     t <= 3'b000;
                 end
             end
                      

             end
         end
         
         assign R1 = mySystem.rf.R1_out;
         assign R2 = mySystem.rf.R2_out;
         assign R3 = mySystem.rf.R3_out;
         assign R4 = mySystem.rf.R4_out;
         assign PC = mySystem.arf.pc_out;
         assign AR = mySystem.arf.ar_out;
         assign SP = mySystem.arf.sp_out;
endmodule