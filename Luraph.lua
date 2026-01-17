local function closeUpvalues(LocalUpvalues, Stack, Value)
    Value = Value or 0

    local Upvalues = {}
    for _, LUpvalues in LocalUpvalues do
        for _, LUpvalue in LUpvalues do
            if LUpvalue[1] == Stack and LUpvalue[2] >= Value then
                local UpvalueIndex = LUpvalue[2]
                if not Upvalues[UpvalueIndex] then
                    Upvalues[UpvalueIndex] = {
                        Stack[UpvalueIndex]
                    }
                end
                LUpvalue[1] = Upvalues[UpvalueIndex]
                LUpvalue[2] = 1
            end
        end
    end
end

local function createUpvalues(UpvalueData, Stack, LocalUpvalues, ProtoUpvalues)
    local Upvalues = nil
    if #UpvalueData > 0 then
        Upvalues = {}
        for UpvalueIndex, Upvalue in UpvalueData do
            if Upvalue[1] == 0 then
                Upvalues[UpvalueIndex - 1] = { Stack, Upvalue[2] }
            else
                Upvalues[UpvalueIndex - 1] = ProtoUpvalues[Upvalue[2]]
            end
        end
        table.insert(LocalUpvalues, Upvalues)
    end
    return Upvalues
end

return (function(NonVirtualizedClosures)
    local BaseXorKey

    local OuterConstantTable = {}
	local OuterConstantHolder = { [2] = OuterConstantTable }

	local LPH_BytecodeIndex = 1
	local LPH_ConstantIndex = 1

	local InlineIndexes = { [3] = 4, [1] = 5, [6] = 2 }
    local ABC_Registers = { [1] = 3, [2] = 1, [3] = 6 }

	local function Count_Pack(...)
		return select("#", ...), {...}
	end

    local function ScaledModuloDivison(Value, Exponent1, Exponent2)
        local Divisor1 = 2^Exponent1
        local Divisor2 = 2^Exponent2
        return (Value / Divisor1) % Divisor2
    end

	local function ReadByte()
        local A = string.byte(LPH_Bytecode, LPH_BytecodeIndex, LPH_BytecodeIndex)
        LPH_BytecodeIndex = LPH_BytecodeIndex + 1
        return A
	end

	local function ReadInt32()
        local A, nextIndex = string.unpack("<I4", LPH_Bytecode, LPH_BytecodeIndex)
        LPH_BytecodeIndex = nextIndex
        return A
    end

    local function ReadInt64()
        local A, nextIndex = string.unpack("<i8", LPH_Bytecode, LPH_BytecodeIndex)
        LPH_BytecodeIndex = nextIndex
        return A
    end

    local function ReadVarInt()
        local result, shift = 0, 0
        while true do
            local byte = string.byte(LPH_Bytecode, LPH_BytecodeIndex, LPH_BytecodeIndex)
            LPH_BytecodeIndex = LPH_BytecodeIndex + 1
            result = result + ((byte > 127 and byte - 128 or byte) * 2^shift)

            if byte < 128 then
                return result
            end

            shift = shift + 7
        end
    end

    local function ReadDouble()
        local A, nextIndex = string.unpack("<d", LPH_Bytecode, LPH_BytecodeIndex)
        LPH_BytecodeIndex = nextIndex
        return A
    end

    local function ReadString(XorKey)
        local EncodedLength, Result = ReadInt32(), ""

        for Index = 1, EncodedLength, 7997 do
            local Length = Index + 7997 - 1

            if Length > EncodedLength then
                Length = EncodedLength
            end

            local Bytes = { string.byte(LPH_Bytecode, LPH_BytecodeIndex + Index - 1, LPH_BytecodeIndex + Length - 1) }

            for ByteIndex = 1, #Bytes do
                Bytes[ByteIndex] = bit32.bxor(Bytes[ByteIndex], BaseXorKey)
                BaseXorKey = (XorKey * BaseXorKey + 87) % 256
            end

            Result = Result .. string.char(unpack(Bytes))
        end

        LPH_BytecodeIndex += EncodedLength

        return Result
    end

    local function ProcessVarInt()
        local A = ReadVarInt()
        if A >= 4503599627370496 then
            return A - 9007199254740992
        end
        return A
    end

    BaseXorKey = ReadByte()

	local function WrapProto(ProtoData, ProtoUpvalues, ProtoEnvironment)
		local Instructions  = ProtoData[6]
        local Prototypes    = ProtoData[1]
		local IsVararg      = ProtoData[7]
        local HasVararg     = ProtoData[9]
        local ParamCount    = ProtoData[4]
		local LUpvalues     = setmetatable({}, { __mode = "v" })

		local function RunVM(...)
            local Stack, StackTop, InstructionPointer =  {}, 0, 1

            local Storage = {
				[1] = ProtoData,
				[2] = Stack
			}

			local ArgumentCount, Arguments = Count_Pack(...)
            ArgumentCount -= 1

			for Index = 0, ArgumentCount do
				if ParamCount > Index then
					Stack[Index] = Arguments[Index + 1]
				else
					break
				end
			end

			if IsVararg then
				if HasVararg then
					Stack[ParamCount] = {
						n = ArgumentCount >= ParamCount and ArgumentCount - ParamCount + 1 or 0,
						unpack(Arguments, ParamCount + 1, ArgumentCount + 1)
					}
                end
			else
				Arguments = nil
			end

			while true do
				local Instruction = Instructions[InstructionPointer]
				local Opcode = Instruction[7]

                local A = Instruction[6]
                local B = Instruction[1]
                local C = Instruction[3]
                local KB = Instruction[5]
                local KC = Instruction[4]

				InstructionPointer += 1
				if Opcode == 0 then
                    local Generator = coroutine.wrap(function(...)
                        coroutine.yield()
                        for Value0, Value1, Value2, Value3, Value4, Value5, Value6, Value7, Value8, Value9 in ... do
                            coroutine.yield(true, { Value0, Value1, Value2, Value3, Value4, Value5, Value6, Value7, Value8, Value9 })
                        end
                    end)
                    Generator(Stack[A], Stack[A + 1], Stack[A + 2])
                    Stack[A] = Generator
                    StackTop = A
                    InstructionPointer = B
                elseif Opcode == 1 then
                    Stack[A] = Stack[B] * Stack[C]
                elseif Opcode == 2 then
                    Stack[A] = Stack[B] < KC
                elseif Opcode == 3 then
                    Stack[A] = KB ^ Stack[C]
                elseif Opcode == 4 then
                    local Result = Stack[B]
                    for Index = B + 1, C do
                        Result ..= Stack[Index]
                    end
                    Stack[A] = Result
                elseif Opcode == 5 then
                    local Start, Limit, Step = Stack[A], Stack[A + 1], Stack[A + 2]
                    Stack[A] = coroutine.wrap(function()
                        for Index = Start, Limit, Step do
                            coroutine.yield(true, Index)
                        end
                    end)
                    InstructionPointer = B
                elseif Opcode == 6 then
                    local Continue, Value = Stack[A]()
                    if Continue then
                        Stack[A + 1] = Value
                        InstructionPointer = B
                    end
                elseif Opcode == 7 then
                    Stack[A] = Stack[B] >= KC
                elseif Opcode == 8 then
                    if Stack[B] <= Stack[C] then
                        InstructionPointer = A
                    end
                elseif Opcode == 9 then
                    if C == 180 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 231, [1] = B - 231, [7] = 62 }
                    else
                        closeUpvalues(LUpvalues, Stack)
                        return unpack(Stack, A, A + B - 2)
                    end
                elseif Opcode == 10 then
                    Stack[A][Stack[B]] = Stack[C]
                elseif Opcode == 11 then
                    local ReturnCount, ReturnTable = nil, nil

                    if B ~= 0 then
                        StackTop = A + B - 1
                    end
                    
                    if B == 1 then
                        ReturnCount, ReturnTable = Count_Pack(Stack[A]())
                    else
                        ReturnCount, ReturnTable = Count_Pack(Stack[A](unpack(Stack, A + 1, StackTop)))
                    end

                    if C == 1 then
                        ReturnCount = -1
                        StackTop = A - 1
                    elseif C == 0 then
                        ReturnCount = ReturnCount + A - 1
                        StackTop = ReturnCount
                    else
                        ReturnCount = A + C - 2
                        StackTop = ReturnCount + 1
                    end

                    table.move(ReturnTable, 1, ReturnCount, A, Stack)
                elseif Opcode == 12 then
                    Stack[A](Stack[A + 1])
                    StackTop = A - 1
                elseif Opcode == 13 then
                    Stack[A] = #Stack[B]
                elseif Opcode == 14 then
                    Stack[A] = Stack[B] ~= KC
                elseif Opcode == 15 then
                    Stack[A] = bit32.bnot(Stack[B])
                elseif Opcode == 16 then
                    Stack[A] = KB + Stack[C]
                elseif Opcode == 17 then
                    Stack[A] = Stack[B] % KC
                elseif Opcode == 18 then
                    Stack[A] = Stack[B] > KC
                elseif Opcode == 19 then
                    Stack[A] = KB
                elseif Opcode == 20 then
                    local Upvalue = ProtoUpvalues[B]
                    Upvalue[1][Upvalue[2]] = Stack[A]
                elseif Opcode == 21 then
                    closeUpvalues(LUpvalues, Stack)
                    return Stack[A]()
                elseif Opcode == 22 then
                    Stack[A] = true
                elseif Opcode == 23 then
                    Stack[A] = not Stack[B]
                elseif Opcode == 24 then
                    if C == 164 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 114, [1] = B - 114, [7] = 37 }
                    else
                        Stack[A] = Arguments[ParamCount + 1]
                    end
                elseif Opcode == 25 then
                    local Prototype = Prototypes[B]
                    local NewUpvalues = createUpvalues(Prototype[5], Stack, LUpvalues, ProtoUpvalues)
                    Stack[A] = NonVirtualizedClosures[C](NewUpvalues)
                elseif Opcode == 26 then
                    local Continue, Values = Stack[A]()
                    if Continue then
                        table.move(Values, 1, C, A, Stack)
                        InstructionPointer = B
                    end
                elseif Opcode == 27 then
                    Stack[A] = KB - KC
                elseif Opcode == 28 then
                    ProtoEnvironment[KB] = Stack[A]
                elseif Opcode == 29 then
                    local Prototype = Prototypes[B]
                    local NewUpvalues = createUpvalues(Prototype[5], Stack, LUpvalues, ProtoUpvalues)
                    Stack[A] = WrapProto(Prototype, NewUpvalues, ProtoEnvironment)
                elseif Opcode == 30 then
                    if Stack[B] == KC then
                        InstructionPointer = A
                    end
                elseif Opcode == 31 then
                    if Stack[B] ~= Stack[C] then
                        InstructionPointer = A
                    end
                elseif Opcode == 32 then
                    Stack[A] = ProtoEnvironment[KB]
                elseif Opcode == 33 then
                    if Stack[A] then
                        InstructionPointer = B
                    end
                elseif Opcode == 34 then
                    Stack[A] = Stack[B] .. Stack[B + 1]
                elseif Opcode == 35 then
                    StackTop = A
                    Stack[StackTop] = Stack[StackTop]()
                elseif Opcode == 36 then
                    if Stack[B] ~= KC then
                        InstructionPointer = A
                    end
                elseif Opcode == 37 then
                    Stack[A] = nil
                elseif Opcode == 38 then
                    local Object = Stack[B]
                    Stack[A + 1] = Object
                    Stack[A] = Object[KC]
                elseif Opcode == 39 then
                    Stack[A] = KB >= Stack[C]
                elseif Opcode == 40 then
                    Stack[A] = Stack[B] < Stack[C]
                elseif Opcode == 41 then
                    Stack[A] = KB * Stack[C]
                elseif Opcode == 42 then
                    Stack[A] = Stack[B] - Stack[C]
                elseif Opcode == 43 then
                    Stack[A] = Storage[B]
                elseif Opcode == 44 then
                    Stack[A] = Stack[B] >= Stack[C]
                elseif Opcode == 45 then
                    if C == 22 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 71, [1] = B - 71, [7] = 9 }
                    elseif C ~= 206 then
                        closeUpvalues(LUpvalues, Stack, A)
                    else
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 17, [1] = B - 17, [7] = 76 }
                    end
                elseif Opcode == 46 then
                    Stack[A] = Stack[B] ^ Stack[C]
                elseif Opcode == 47 then
                    Stack[A] = Stack[A](Stack[A + 1])
                    StackTop = A
                elseif Opcode == 48 then
                    Stack[A] = -Stack[B]
                elseif Opcode == 49 then
                    local Continue, Index, Value = Stack[A]()
                    if Continue then
                        Stack[A + 1] = Index
                        Stack[A + 2] = Value
                        InstructionPointer = B
                    end
                elseif Opcode == 50 then
                    closeUpvalues(LUpvalues, Stack)
                    return Stack[A]
                elseif Opcode == 51 then
                    local Continue, Value = Stack[A]()
                    if Continue then
                        Stack[A + 3] = Value
                        InstructionPointer = B
                    end
                elseif Opcode == 52 then
                    Stack[A] = Stack[B] <= KC
                elseif Opcode == 53 then
                    Stack[A] = KB ~= KC
                elseif Opcode == 54 then
                    StackTop = A
                    Stack[StackTop]()
                    StackTop = StackTop - 1
                elseif Opcode == 55 then
                    Stack[A] = Stack[B] / KC
                elseif Opcode == 56 then
                    local Upvalue = ProtoUpvalues[B]
                    Stack[A] = Upvalue[1][Upvalue[2]]
                elseif Opcode == 57 then
                    Stack[A][KB] = Stack[C]
                elseif Opcode == 58 then
                    if KB > Stack[C] then
                        InstructionPointer = A
                    end
                elseif Opcode == 59 then
                    if C == 165 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 33, [1] = B - 33, [7] = 62 }
                    else
                        closeUpvalues(LUpvalues, Stack)
                        return unpack(Stack, A, StackTop)
                    end
                elseif Opcode == 60 then
                    Stack[A] = { unpack({}, 1, B) }
                elseif Opcode == 61 then
                    Stack[A] = Stack[B] > Stack[C]
                elseif Opcode == 62 then
                    if C == 15 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 72, [1] = B - 72, [7] = 50 }
                    elseif C == 26 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 127, [1] = B - 127, [7] = 48 }
                    else
                        local VarargCount = ArgumentCount - ParamCount
                        if VarargCount < 0 then
                            VarargCount = -1
                        end

                        for Index = A, A + VarargCount do
                            Stack[Index] = Arguments[ParamCount + (Index - A) + 1]
                        end

                        StackTop = A + VarargCount
                    end
                elseif Opcode == 63 then
                    if C == 85 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 187, [1] = B - 187, [7] = 13 }
                    elseif C == 201 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 244, [1] = B - 244, [7] = 90 }
                    elseif C == 136 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 127, [1] = B - 127, [7] = 23 }
                    else
                        table.move(Arguments, ParamCount + 1, ParamCount + B, A, Stack)
                    end
                elseif Opcode == 64 then
                    Stack[A](Stack[A + 1], Stack[A + 2])
                    StackTop = A - 1
                elseif Opcode == 65 then
                    Stack[A](unpack(Stack, A + 1, StackTop))
                    StackTop = A - 1
                elseif Opcode == 66 then
                    Stack[A] = bit32.bor(Stack[B], Stack[C])
                elseif Opcode == 67 then
                    Stack[A] = Stack[B] ~= Stack[C]
                elseif Opcode == 68 then
                    local Block = (C - 1) * 50
                    local Table = Stack[A]
                    for Index = 1, B do
                        Table[Block + Index] = Stack[A + Index]
                    end
                elseif Opcode == 69 then
                    local Value = Stack[B] / Stack[C]
                    Stack[A] = Value - Value % 1
                elseif Opcode == 70 then
                    Stack[A] = Stack[A](Stack[A + 1], Stack[A + 2])
                    StackTop = A
                elseif Opcode == 71 then
                    local Generator = coroutine.wrap(function(...)
                        coroutine.yield()
                        for Index in ... do
                            coroutine.yield(true, Index)
                        end
                    end)
                    Generator(Stack[A], Stack[A + 1], Stack[A + 2])
                    Stack[A] = Generator
                    StackTop = A
                    InstructionPointer = B
                elseif Opcode == 72 then
                    closeUpvalues(LUpvalues, Stack)
                    return Stack[A](unpack(Stack, A + 1, A + B - 1))
                elseif Opcode == 73 then
                    Stack[A] = Stack[B][KC]
                elseif Opcode == 74 then
                    Stack[A] = Stack[B] % Stack[C]
                elseif Opcode == 75 then
                    Stack[A] = bit32.bxor(Stack[B], Stack[C])
                elseif Opcode == 76 then
                    if C == 83 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 8, [1] = B - 8, [7] = 45 }
                    elseif C == 167 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 234, [1] = B - 234, [7] = 37 }
                    else
                        for Index = A, B do
                            Stack[Index] = nil
                        end
                    end
                elseif Opcode == 77 then
                    Stack[A] = bit32.rshift(Stack[B], Stack[C])
                elseif Opcode == 78 then
                    Stack[A][KB] = KC
                elseif Opcode == 79 then
                    Storage[B] = Stack[A]
                elseif Opcode == 80 then
                    Stack[A] = Stack[B] <= Stack[C]
                elseif Opcode == 81 then
                    Stack[A](unpack(Stack, A + 1, A + B - 1))
                    StackTop = A - 1
                elseif Opcode == 82 then
                    Stack[A] = Stack[B] / Stack[C]
                elseif Opcode == 83 then
                    Stack[A] = Stack[B] == KC
                elseif Opcode == 84 then
                    Stack[A][Stack[B]] = KC
                elseif Opcode == 85 then
                    local Table = Stack[A]
                    local Block = (C - 1) * 50

                    for Index = 1, StackTop - A do
                        Table[Block + Index] = Stack[A + Index]
                    end
                elseif Opcode == 86 then
                    if Stack[B] < Stack[C] then
                        InstructionPointer = A
                    end
                elseif Opcode == 87 then
                    Stack[A] = Stack[B] + Stack[C]
                elseif Opcode == 88 then
                    if Stack[B] >= Stack[C] then
                        InstructionPointer = A
                    end
                elseif Opcode == 89 then
                    Stack[A] = Stack[B] - KC
                elseif Opcode == 90 then
                    if C == 113 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 158, [1] = B - 158, [7] = 9 }
                    elseif C ~= 82 then
                        Stack[A] = Stack[B]
                    else
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 40, [1] = B - 40, [7] = 93 }
                    end
                elseif Opcode == 91 then
                    Stack[A] = {}
                elseif Opcode == 92 then
                    if Stack[B] == Stack[C] then
                        InstructionPointer = A
                    end
                elseif Opcode == 93 then
                    if C == 125 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 137, [1] = B - 137, [7] = 50 }
                    elseif C == 94 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 169, [1] = B - 169, [7] = 24 }
                    else
                        closeUpvalues(LUpvalues, Stack)
                        return
                    end
                elseif Opcode == 94 then
                    OuterConstantHolder[B] = Stack[A]
                elseif Opcode == 95 then
                    Stack[A] = Stack[B] * KC
                elseif Opcode == 96 then
                    StackTop = A + B - 1
                    Stack[A] = Stack[A](unpack(Stack, A + 1, StackTop))
                    StackTop = A
                elseif Opcode == 97 then
                    Stack[A] = bit32.lshift(Stack[B], Stack[C])
                elseif Opcode == 98 then
                    local Generator = coroutine.wrap(function(...)
                        coroutine.yield()
                        for Index, Value in ... do
                            coroutine.yield(true, Index, Value)
                        end
                    end)
                    Generator(Stack[A], Stack[A + 1], Stack[A + 2])
                    Stack[A] = Generator
                    StackTop = A
                    InstructionPointer = B
                elseif Opcode == 99 then
                    closeUpvalues(LUpvalues, Stack)
                    return Stack[A](unpack(Stack, A + 1, StackTop))
                elseif Opcode == 100 then
                    Stack[A] = OuterConstantHolder[B]
                elseif Opcode == 101 then
                    if Stack[B] < Stack[C] then
                        InstructionPointer = A
                    end
                elseif Opcode == 102 then
                    Stack[A] = Stack[B][Stack[C]]
                elseif Opcode == 103 then
                    Stack[A] = Stack[B] + KC
                elseif Opcode == 104 then
                    Stack[A] = Stack[A](unpack(Stack, A + 1, StackTop))
                    StackTop = A
                elseif Opcode == 105 then
                    Stack[A] = bit32.band(Stack[B], Stack[C])
                elseif Opcode == 106 then
                    if C == 59 then
                        InstructionPointer -= 1
                        Instructions[InstructionPointer] = { [6] = A - 145, [1] = B - 145, [7] = 59 }
                    else
                        if not Stack[A] then
                            InstructionPointer = B
                        end
                    end
                elseif Opcode == 107 then
                    Stack[A] = Stack[B] == Stack[C]
                else
                    InstructionPointer = B
                end
			end
		end

		setfenv(RunVM, ProtoEnvironment)
		return RunVM
	end

	local function Deserialize()
        local ConstantIndex, Constants, ConstantIndexMap = 1, {}, {}
        local Prototypes, Instructions, Upvalues = {}, {}, {}

        local Chunk = { Prototypes, nil, {}, nil, Upvalues, Instructions, nil, nil, nil }

		local InstructionsSize = ReadInt32() - 50981
        for Index = 1, InstructionsSize do
            local VarInt1, VarInt2, Opcode, VarInt3 = ProcessVarInt(), ProcessVarInt(), ProcessVarInt(), ProcessVarInt()
            local VarInt1_Mod, VarInt2_Mod, VarInt3_Mod = VarInt1 % 4, VarInt2 % 4, VarInt3 % 4
            
            Instructions[Index] = {
                [1] = (VarInt3 - VarInt3_Mod) / 4,
                [2] = VarInt1_Mod,
                [3] = (VarInt2 - VarInt2_Mod) / 4,
                [4] = VarInt2_Mod,
                [5] = VarInt3_Mod,
                [6] = (VarInt1 - VarInt1_Mod) / 4,
                [7] = Opcode
            }
        end

        Chunk[4] = ReadVarInt()
        Chunk[8] = ReadVarInt()

        local IsVararg = ReadByte()

        Chunk[7] = ScaledModuloDivison(IsVararg, 1, 1) ~= 0
        Chunk[9] = ScaledModuloDivison(IsVararg, 2, 1) ~= 0

        local PrototypesSize = ReadInt32() - 9786
        for Index = 0, PrototypesSize - 1 do
            Prototypes[Index] = Deserialize()
        end

        Chunk[2] = ReadVarInt()
        Chunk[19] = ReadInt32()
        Chunk[12] = ReadInt32()
        Chunk[17] = ReadInt32()
        Chunk[10] = ReadByte()
        Chunk[19] = ReadInt32()
        Chunk[14] = ReadByte()

        local ConstantsSize = ReadInt32() - 37102

		local ProtoXorKey = ReadByte()
		local ConstantEncryption = ReadByte() ~= 0

        for Index = 1, ConstantsSize do
            local ConstantType = ReadByte()

            local Constant = nil
            if ConstantType == 44 then
                Constant = string.sub(ReadString(ProtoXorKey), 5)
            elseif ConstantType == 62 then
                Constant = ReadInt64()
            elseif ConstantType == 193 then
                Constant = ReadByte() == 1
            elseif ConstantType == 155 then
                Constant = ReadDouble()
            end

            local ConstantTable = { Constant, {} }

            ConstantIndex += 1

            ConstantIndexMap[Index - 1] = ConstantIndex
            Constants[ConstantIndex] = ConstantTable

            if ConstantEncryption then
                OuterConstantTable[LPH_ConstantIndex] = ConstantTable
                LPH_ConstantIndex += 1
            end
        end

        for Index = 1, InstructionsSize do
            local Instruction = Instructions[Index]

            for _, RegisterIndex in next, ABC_Registers do
                local InlineIndex = InlineIndexes[RegisterIndex]
                local InliningType = Instruction[InlineIndex]

                if InliningType == 0 then
                    Instruction[RegisterIndex] = Index + Instruction[RegisterIndex] + 1
                elseif InliningType == 1 then
                    local ConstantIdx = ConstantIndexMap[Instruction[RegisterIndex]]
                    local Constant = Constants[ConstantIdx]
                    if Constant then
                        Instruction[InlineIndex] = Constant[1]
                        local ConstantReferences = Constant[2]

                        ConstantReferences[#ConstantReferences + 1] = { Instruction, InlineIndex }
                    end
                end
            end
        end

		for Index = 1, ReadVarInt() do
			Upvalues[Index] = {
				ReadByte(),
				ReadVarInt()
			}
		end

        Chunk[15] = ReadByte()
        Chunk[14] = ReadInt32()
        Chunk[14] = ReadInt32()
        Chunk[11] = ReadByte()

        return Chunk
    end

    local Environment = getfenv()

	local MainChunk = Deserialize()
    MainChunk = WrapProto(MainChunk, nil, Environment)(Deserialize, function(...)
        (...)[...] = nil
    end, function(...)
        return (...)[...]
    end, function(...)
        return (...)()
    end, ReadDouble, ReadByte, ReadInt32, { 
        14823, 
        2676198886, 
        3018667413, 
        349335283, 
        4106820334, 
        3479301002, 
        3760799924, 
        1234350129, 
        3502622987 
    })
    return WrapProto(MainChunk, nil, Environment)
end)({})(...)
