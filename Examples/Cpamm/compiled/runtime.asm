// Labelled pre-assembly (powdr YulEvmCompiler.Asm, before lowerProg).
// Each `Ln:` is a JUMPDEST. JUMP/JUMPI take labels, not byte offsets.
// selector → function  (hex and decimal; `switch` cases print decimal)
//   0x9cd441da  (2631156186)  addLiquidity(uint256,uint256)
//   0x9c8f9f23  (2626658083)  removeLiquidity(uint256)
//   0x2b1087f0  (722503664)  swap0for1(uint256,uint256)
//   0x21d2da23  (567466531)  swap1for0(uint256,uint256)
//   0xce9c0bb7  (3466333111)  setProtocolShare(uint256)
//   0xf46901ed  (4100522477)  setFeeTo(address)
//   0xa1af5b9a  (2712624026)  collectProtocolFees()
//   0x0902f1ac  (151187884)  getReserves()
//   0xf5eb42dc  (4125835996)  sharesOf(address)
//   0x1ad8b03b  (450408507)  protocolFees()

    PUSH 0x0180
    ISZERO
    POP
    PUSH 0x00
    TLOAD
    ISZERO
    JUMPI L1
    PUSH 0x00
    PUSH 0x00
    REVERT
L1:    // JUMPDEST
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L2
    PUSH 0x00
    PUSH 0x00
    REVERT
L2:    // JUMPDEST
    PUSH 0x00
    CALLDATALOAD
    PUSH 0xe0
    SHR
    DUP1
    PUSH 0x9cd441da    // selector: addLiquidity(uint256,uint256)
    EQ
    JUMPI L4
    DUP1
    PUSH 0x9c8f9f23    // selector: removeLiquidity(uint256)
    EQ
    JUMPI L140
    DUP1
    PUSH 0x2b1087f0    // selector: swap0for1(uint256,uint256)
    EQ
    JUMPI L161
    DUP1
    PUSH 0x21d2da23    // selector: swap1for0(uint256,uint256)
    EQ
    JUMPI L204
    DUP1
    PUSH 0xce9c0bb7    // selector: setProtocolShare(uint256)
    EQ
    JUMPI L247
    DUP1
    PUSH 0xf46901ed    // selector: setFeeTo(address)
    EQ
    JUMPI L251
    DUP1
    PUSH 0xa1af5b9a    // selector: collectProtocolFees()
    EQ
    JUMPI L254
    DUP1
    PUSH 0x0902f1ac    // selector: getReserves()
    EQ
    JUMPI L264
    DUP1
    PUSH 0xf5eb42dc    // selector: sharesOf(address)
    EQ
    JUMPI L266
    DUP1
    PUSH 0x1ad8b03b    // selector: protocolFees()
    EQ
    JUMPI L268
    POP
    PUSH 0x00
    PUSH 0x00
    REVERT
    JUMP L3
L4:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L5
    PUSH 0x00
    PUSH 0x00
    REVERT
L5:    // JUMPDEST
    PUSH 0x01
    PUSH 0x00
    TSTORE
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x0100
    MSTORE
    PUSH 0x24
    CALLDATALOAD
    PUSH 0x0120
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0x00
    LT
    JUMPI L6
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L6:    // JUMPDEST
    PUSH 0x0120
    MLOAD
    PUSH 0x00
    LT
    JUMPI L7
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L7:    // JUMPDEST
    CALLER
    PUSH 0x0140
    MSTORE
    ADDRESS
    PUSH 0x0160
    MSTORE
    PUSH 0x02
    SLOAD
    PUSH 0x03
    SLOAD
    PUSH 0x04
    SLOAD
    PUSH 0x00
    DUP2
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L9
    POP
    PUSH 0x0100
    MLOAD
    DUP1
    PUSH 0x03e8
    LT
    JUMPI L98
    PUSH 0xbb55fd27    // selector: InsufficientLiquidity()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L98:    // JUMPDEST
    PUSH 0x03e8
    DUP2
    LT
    ISZERO
    JUMPI L99
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L99:    // JUMPDEST
    PUSH 0x03e8
    DUP2
    SUB
    DUP1
    PUSH 0x00
    LT
    JUMPI L100
    PUSH 0x9811e0c7    // selector: ZeroShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L100:    // JUMPDEST
    PUSH 0x0100
    MLOAD
    DUP6
    ADD
    DUP6
    DUP2
    LT
    ISZERO
    JUMPI L101
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L101:    // JUMPDEST
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0120
    MLOAD
    DUP6
    ADD
    DUP6
    DUP2
    LT
    ISZERO
    JUMPI L102
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L102:    // JUMPDEST
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x00
    DUP6
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L104
    POP
    PUSH 0x0100
    MLOAD
    DUP6
    ADD
    DUP6
    DUP2
    LT
    ISZERO
    JUMPI L122
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L122:    // JUMPDEST
    DUP1
    PUSH 0x04
    SSTORE
    PUSH 0x00
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x03e8
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    DUP7
    EQ
    ISZERO
    DUP1
    PUSH 0x00
    EQ
    JUMPI L124
    POP
    DUP4
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L132
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L132:    // JUMPDEST
    DUP1
    PUSH 0x04
    SSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP6
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L133
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L133:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L134
    PUSH 0x00
    PUSH 0x00
    REVERT
L134:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L135
    PUSH 0x00
    PUSH 0x00
    REVERT
L135:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L136
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L136:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L137
    PUSH 0x00
    PUSH 0x00
    REVERT
L137:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L138
    PUSH 0x00
    PUSH 0x00
    REVERT
L138:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L139
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L139:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP11
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP11
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L123
L124:    // JUMPDEST
    POP
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L125
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L125:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L126
    PUSH 0x00
    PUSH 0x00
    REVERT
L126:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L127
    PUSH 0x00
    PUSH 0x00
    REVERT
L127:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L128
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L128:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L129
    PUSH 0x00
    PUSH 0x00
    REVERT
L129:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L130
    PUSH 0x00
    PUSH 0x00
    REVERT
L130:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L131
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L131:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP10
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP10
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
L123:    // JUMPDEST
    POP
    JUMP L103
L104:    // JUMPDEST
    POP
    PUSH 0x00
    DUP6
    EQ
    ISZERO
    DUP1
    PUSH 0x00
    EQ
    JUMPI L106
    POP
    DUP3
    DUP6
    ADD
    DUP6
    DUP2
    LT
    ISZERO
    JUMPI L114
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L114:    // JUMPDEST
    DUP1
    PUSH 0x04
    SSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L115
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L115:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L116
    PUSH 0x00
    PUSH 0x00
    REVERT
L116:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L117
    PUSH 0x00
    PUSH 0x00
    REVERT
L117:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L118
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L118:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L119
    PUSH 0x00
    PUSH 0x00
    REVERT
L119:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L120
    PUSH 0x00
    PUSH 0x00
    REVERT
L120:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L121
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L121:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP10
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP10
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L105
L106:    // JUMPDEST
    POP
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP4
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L107
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L107:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L108
    PUSH 0x00
    PUSH 0x00
    REVERT
L108:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L109
    PUSH 0x00
    PUSH 0x00
    REVERT
L109:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L110
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L110:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L111
    PUSH 0x00
    PUSH 0x00
    REVERT
L111:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L112
    PUSH 0x00
    PUSH 0x00
    REVERT
L112:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L113
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L113:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP9
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP9
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
L105:    // JUMPDEST
L103:    // JUMPDEST
    POP
    POP
    POP
    POP
    JUMP L8
L9:    // JUMPDEST
    POP
    DUP3
    PUSH 0x00
    LT
    JUMPI L10
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L10:    // JUMPDEST
    DUP2
    PUSH 0x00
    LT
    JUMPI L11
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L11:    // JUMPDEST
    DUP3
    JUMPI L12
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L12:    // JUMPDEST
    PUSH 0x0100
    MLOAD
    DUP2
    MUL
    PUSH 0x0100
    MLOAD
    DUP3
    DUP3
    DIV
    EQ
    DUP3
    ISZERO
    OR
    JUMPI L13
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L13:    // JUMPDEST
    DUP4
    DUP2
    DIV
    SWAP1
    POP
    DUP3
    JUMPI L14
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L14:    // JUMPDEST
    PUSH 0x0120
    MLOAD
    DUP3
    MUL
    PUSH 0x0120
    MLOAD
    DUP4
    DUP3
    DIV
    EQ
    DUP4
    ISZERO
    OR
    JUMPI L15
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L15:    // JUMPDEST
    DUP4
    DUP2
    DIV
    SWAP1
    POP
    DUP2
    DUP2
    LT
    ISZERO
    DUP1
    PUSH 0x00
    EQ
    JUMPI L17
    POP
    DUP2
    DUP1
    PUSH 0x00
    LT
    JUMPI L58
    PUSH 0x9811e0c7    // selector: ZeroShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L58:    // JUMPDEST
    PUSH 0x0100
    MLOAD
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L59
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L59:    // JUMPDEST
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0120
    MLOAD
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L60
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L60:    // JUMPDEST
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x00
    DUP7
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L62
    POP
    PUSH 0x0100
    MLOAD
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L80
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L80:    // JUMPDEST
    DUP1
    PUSH 0x04
    SSTORE
    PUSH 0x00
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x03e8
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    DUP8
    EQ
    ISZERO
    DUP1
    PUSH 0x00
    EQ
    JUMPI L82
    POP
    DUP4
    DUP8
    ADD
    DUP8
    DUP2
    LT
    ISZERO
    JUMPI L90
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L90:    // JUMPDEST
    DUP1
    PUSH 0x04
    SSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP6
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L91
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L91:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L92
    PUSH 0x00
    PUSH 0x00
    REVERT
L92:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L93
    PUSH 0x00
    PUSH 0x00
    REVERT
L93:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L94
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L94:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L95
    PUSH 0x00
    PUSH 0x00
    REVERT
L95:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L96
    PUSH 0x00
    PUSH 0x00
    REVERT
L96:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L97
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L97:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP11
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP11
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L81
L82:    // JUMPDEST
    POP
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L83
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L83:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L84
    PUSH 0x00
    PUSH 0x00
    REVERT
L84:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L85
    PUSH 0x00
    PUSH 0x00
    REVERT
L85:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L86
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L86:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L87
    PUSH 0x00
    PUSH 0x00
    REVERT
L87:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L88
    PUSH 0x00
    PUSH 0x00
    REVERT
L88:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L89
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L89:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP10
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP10
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
L81:    // JUMPDEST
    POP
    JUMP L61
L62:    // JUMPDEST
    POP
    PUSH 0x00
    DUP7
    EQ
    ISZERO
    DUP1
    PUSH 0x00
    EQ
    JUMPI L64
    POP
    DUP3
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L72
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L72:    // JUMPDEST
    DUP1
    PUSH 0x04
    SSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L73
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L73:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L74
    PUSH 0x00
    PUSH 0x00
    REVERT
L74:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L75
    PUSH 0x00
    PUSH 0x00
    REVERT
L75:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L76
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L76:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L77
    PUSH 0x00
    PUSH 0x00
    REVERT
L77:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L78
    PUSH 0x00
    PUSH 0x00
    REVERT
L78:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L79
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L79:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP10
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP10
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L63
L64:    // JUMPDEST
    POP
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP4
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L65
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L65:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L66
    PUSH 0x00
    PUSH 0x00
    REVERT
L66:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L67
    PUSH 0x00
    PUSH 0x00
    REVERT
L67:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L68
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L68:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L69
    PUSH 0x00
    PUSH 0x00
    REVERT
L69:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L70
    PUSH 0x00
    PUSH 0x00
    REVERT
L70:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L71
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L71:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP9
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP9
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
L63:    // JUMPDEST
L61:    // JUMPDEST
    POP
    POP
    POP
    JUMP L16
L17:    // JUMPDEST
    POP
    DUP1
    DUP1
    PUSH 0x00
    LT
    JUMPI L18
    PUSH 0x9811e0c7    // selector: ZeroShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L18:    // JUMPDEST
    PUSH 0x0100
    MLOAD
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L19
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L19:    // JUMPDEST
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0120
    MLOAD
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L20
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L20:    // JUMPDEST
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x00
    DUP7
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L22
    POP
    PUSH 0x0100
    MLOAD
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L40
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L40:    // JUMPDEST
    DUP1
    PUSH 0x04
    SSTORE
    PUSH 0x00
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x03e8
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    DUP8
    EQ
    ISZERO
    DUP1
    PUSH 0x00
    EQ
    JUMPI L42
    POP
    DUP4
    DUP8
    ADD
    DUP8
    DUP2
    LT
    ISZERO
    JUMPI L50
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L50:    // JUMPDEST
    DUP1
    PUSH 0x04
    SSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP6
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L51
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L51:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L52
    PUSH 0x00
    PUSH 0x00
    REVERT
L52:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L53
    PUSH 0x00
    PUSH 0x00
    REVERT
L53:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L54
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L54:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L55
    PUSH 0x00
    PUSH 0x00
    REVERT
L55:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L56
    PUSH 0x00
    PUSH 0x00
    REVERT
L56:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L57
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L57:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP11
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP11
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L41
L42:    // JUMPDEST
    POP
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L43
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L43:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L44
    PUSH 0x00
    PUSH 0x00
    REVERT
L44:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L45
    PUSH 0x00
    PUSH 0x00
    REVERT
L45:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L46
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L46:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L47
    PUSH 0x00
    PUSH 0x00
    REVERT
L47:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L48
    PUSH 0x00
    PUSH 0x00
    REVERT
L48:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L49
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L49:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP10
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP10
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
L41:    // JUMPDEST
    POP
    JUMP L21
L22:    // JUMPDEST
    POP
    PUSH 0x00
    DUP7
    EQ
    ISZERO
    DUP1
    PUSH 0x00
    EQ
    JUMPI L24
    POP
    DUP3
    DUP7
    ADD
    DUP7
    DUP2
    LT
    ISZERO
    JUMPI L32
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L32:    // JUMPDEST
    DUP1
    PUSH 0x04
    SSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L33
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L33:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L34
    PUSH 0x00
    PUSH 0x00
    REVERT
L34:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L35
    PUSH 0x00
    PUSH 0x00
    REVERT
L35:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L36
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L36:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L37
    PUSH 0x00
    PUSH 0x00
    REVERT
L37:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L38
    PUSH 0x00
    PUSH 0x00
    REVERT
L38:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L39
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L39:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP10
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP10
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L23
L24:    // JUMPDEST
    POP
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP4
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L25
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L25:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L26
    PUSH 0x00
    PUSH 0x00
    REVERT
L26:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L27
    PUSH 0x00
    PUSH 0x00
    REVERT
L27:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L28
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L28:    // JUMPDEST
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x0140
    MLOAD
    PUSH 0x84
    MSTORE
    PUSH 0x0160
    MLOAD
    PUSH 0xa4
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L29
    PUSH 0x00
    PUSH 0x00
    REVERT
L29:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L30
    PUSH 0x00
    PUSH 0x00
    REVERT
L30:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L31
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L31:    // JUMPDEST
    PUSH 0x0140
    MLOAD
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    PUSH 0x0120
    MLOAD
    PUSH 0xc0
    MSTORE
    DUP9
    PUSH 0xe0
    MSTORE
    PUSH 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce    // topic: AddLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP9
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
L23:    // JUMPDEST
L21:    // JUMPDEST
    POP
    POP
    POP
L16:    // JUMPDEST
    POP
    POP
L8:    // JUMPDEST
    POP
    POP
    POP
    JUMP L3
L140:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L141
    PUSH 0x00
    PUSH 0x00
    REVERT
L141:    // JUMPDEST
    PUSH 0x01
    PUSH 0x00
    TSTORE
    PUSH 0x04
    CALLDATALOAD
    DUP1
    PUSH 0x00
    LT
    JUMPI L142
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L142:    // JUMPDEST
    CALLER
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP3
    DUP2
    LT
    ISZERO
    JUMPI L143
    PUSH 0x39996567    // selector: InsufficientShares()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L143:    // JUMPDEST
    PUSH 0x02
    SLOAD
    PUSH 0x03
    SLOAD
    PUSH 0x04
    SLOAD
    DUP1
    PUSH 0x00
    LT
    JUMPI L144
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L144:    // JUMPDEST
    DUP1
    JUMPI L145
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L145:    // JUMPDEST
    DUP6
    DUP4
    MUL
    DUP7
    DUP5
    DUP3
    DIV
    EQ
    DUP5
    ISZERO
    OR
    JUMPI L146
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L146:    // JUMPDEST
    DUP2
    DUP2
    DIV
    SWAP1
    POP
    DUP2
    JUMPI L147
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L147:    // JUMPDEST
    DUP7
    DUP4
    MUL
    DUP8
    DUP5
    DUP3
    DIV
    EQ
    DUP5
    ISZERO
    OR
    JUMPI L148
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L148:    // JUMPDEST
    DUP3
    DUP2
    DIV
    SWAP1
    POP
    DUP2
    PUSH 0x00
    LT
    JUMPI L149
    PUSH 0x1078b533    // selector: ZeroOut()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L149:    // JUMPDEST
    DUP1
    PUSH 0x00
    LT
    JUMPI L150
    PUSH 0x1078b533    // selector: ZeroOut()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L150:    // JUMPDEST
    DUP8
    DUP7
    LT
    ISZERO
    JUMPI L151
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L151:    // JUMPDEST
    DUP8
    DUP7
    SUB
    DUP8
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    DUP1
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SSTORE
    DUP9
    DUP5
    LT
    ISZERO
    JUMPI L152
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L152:    // JUMPDEST
    DUP9
    DUP5
    SUB
    DUP1
    PUSH 0x04
    SSTORE
    DUP4
    DUP8
    LT
    ISZERO
    JUMPI L153
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L153:    // JUMPDEST
    DUP4
    DUP8
    SUB
    DUP1
    PUSH 0x02
    SSTORE
    DUP4
    DUP8
    LT
    ISZERO
    JUMPI L154
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L154:    // JUMPDEST
    DUP4
    DUP8
    SUB
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP14
    PUSH 0x84
    MSTORE
    DUP9
    PUSH 0xa4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x44
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L155
    PUSH 0x00
    PUSH 0x00
    REVERT
L155:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L156
    PUSH 0x00
    PUSH 0x00
    REVERT
L156:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L157
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L157:    // JUMPDEST
    PUSH 0x00
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP15
    PUSH 0x84
    MSTORE
    DUP9
    PUSH 0xa4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x44
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L158
    PUSH 0x00
    PUSH 0x00
    REVERT
L158:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L159
    PUSH 0x00
    PUSH 0x00
    REVERT
L159:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L160
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L160:    // JUMPDEST
    DUP15
    PUSH 0x80
    MSTORE
    DUP10
    PUSH 0xa0
    MSTORE
    DUP9
    PUSH 0xc0
    MSTORE
    DUP16
    PUSH 0xe0
    MSTORE
    PUSH 0x59c3a0b60c6ab7deb62e1440c9e72441db6db7dfe514dba8cb18e60c0d896efa    // topic: RemoveLiquidity(address,uint256,uint256,uint256)
    PUSH 0x80
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP10
    PUSH 0x80
    MSTORE
    DUP9
    PUSH 0xa0
    MSTORE
    PUSH 0x40
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L3
L161:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L162
    PUSH 0x00
    PUSH 0x00
    REVERT
L162:    // JUMPDEST
    PUSH 0x01
    PUSH 0x00
    TSTORE
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x0100
    MSTORE
    PUSH 0x24
    CALLDATALOAD
    PUSH 0x0100
    MLOAD
    PUSH 0x00
    LT
    JUMPI L163
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L163:    // JUMPDEST
    PUSH 0x02
    SLOAD
    PUSH 0x03
    SLOAD
    DUP2
    PUSH 0x00
    LT
    JUMPI L164
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L164:    // JUMPDEST
    DUP1
    PUSH 0x00
    LT
    JUMPI L165
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L165:    // JUMPDEST
    PUSH 0x07
    SLOAD
    PUSH 0x08
    SLOAD
    PUSH 0x2710
    JUMPI L166
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L166:    // JUMPDEST
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    MUL
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    DUP3
    DIV
    EQ
    PUSH 0x0100
    MLOAD
    ISZERO
    OR
    JUMPI L167
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L167:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    DUP6
    ADD
    DUP6
    DUP2
    LT
    ISZERO
    JUMPI L168
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L168:    // JUMPDEST
    DUP1
    JUMPI L169
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L169:    // JUMPDEST
    DUP2
    DUP6
    MUL
    DUP3
    DUP7
    DUP3
    DIV
    EQ
    DUP7
    ISZERO
    OR
    JUMPI L170
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L170:    // JUMPDEST
    DUP2
    DUP2
    DIV
    SWAP1
    POP
    DUP3
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L171
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L171:    // JUMPDEST
    DUP3
    PUSH 0x0100
    MLOAD
    SUB
    PUSH 0x00
    DUP7
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L173
    POP
    PUSH 0x2710
    JUMPI L189
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L189:    // JUMPDEST
    PUSH 0x00
    DUP2
    MUL
    PUSH 0x00
    DUP3
    DUP3
    DIV
    EQ
    DUP3
    ISZERO
    OR
    JUMPI L190
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L190:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    DUP3
    LT
    ISZERO
    JUMPI L191
    PUSH 0xcd4e6167    // selector: FeeTooHigh()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L191:    // JUMPDEST
    DUP10
    DUP4
    LT
    ISZERO
    JUMPI L192
    PUSH 0xbb2875c3    // selector: InsufficientOutput()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L192:    // JUMPDEST
    DUP3
    PUSH 0x00
    LT
    JUMPI L193
    PUSH 0x1078b533    // selector: ZeroOut()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L193:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L194
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L194:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    DUP1
    DUP11
    ADD
    DUP11
    DUP2
    LT
    ISZERO
    JUMPI L195
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L195:    // JUMPDEST
    DUP1
    PUSH 0x02
    SSTORE
    DUP5
    DUP11
    LT
    ISZERO
    JUMPI L196
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L196:    // JUMPDEST
    DUP5
    DUP11
    SUB
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x09
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L197
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L197:    // JUMPDEST
    DUP1
    PUSH 0x09
    SSTORE
    CALLER
    ADDRESS
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0x84
    MSTORE
    DUP4
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L198
    PUSH 0x00
    PUSH 0x00
    REVERT
L198:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L199
    PUSH 0x00
    PUSH 0x00
    REVERT
L199:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L200
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L200:    // JUMPDEST
    PUSH 0x00
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP6
    PUSH 0x84
    MSTORE
    DUP14
    PUSH 0xa4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x44
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L201
    PUSH 0x00
    PUSH 0x00
    REVERT
L201:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L202
    PUSH 0x00
    PUSH 0x00
    REVERT
L202:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L203
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L203:    // JUMPDEST
    DUP6
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    DUP14
    PUSH 0xc0
    MSTORE
    PUSH 0x268d208c45ec3d7213f545c4402b1bc7f11b332757a4e0d84ff4d37b90db1fca    // topic: Swap0for1(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP14
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L172
L173:    // JUMPDEST
    POP
    PUSH 0x2710
    JUMPI L174
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L174:    // JUMPDEST
    DUP5
    DUP2
    MUL
    DUP6
    DUP3
    DUP3
    DIV
    EQ
    DUP3
    ISZERO
    OR
    JUMPI L175
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L175:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    DUP3
    LT
    ISZERO
    JUMPI L176
    PUSH 0xcd4e6167    // selector: FeeTooHigh()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L176:    // JUMPDEST
    DUP10
    DUP4
    LT
    ISZERO
    JUMPI L177
    PUSH 0xbb2875c3    // selector: InsufficientOutput()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L177:    // JUMPDEST
    DUP3
    PUSH 0x00
    LT
    JUMPI L178
    PUSH 0x1078b533    // selector: ZeroOut()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L178:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L179
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L179:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    DUP1
    DUP11
    ADD
    DUP11
    DUP2
    LT
    ISZERO
    JUMPI L180
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L180:    // JUMPDEST
    DUP1
    PUSH 0x02
    SSTORE
    DUP5
    DUP11
    LT
    ISZERO
    JUMPI L181
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L181:    // JUMPDEST
    DUP5
    DUP11
    SUB
    DUP1
    PUSH 0x03
    SSTORE
    PUSH 0x09
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L182
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L182:    // JUMPDEST
    DUP1
    PUSH 0x09
    SSTORE
    CALLER
    ADDRESS
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0x84
    MSTORE
    DUP4
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L183
    PUSH 0x00
    PUSH 0x00
    REVERT
L183:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L184
    PUSH 0x00
    PUSH 0x00
    REVERT
L184:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L185
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L185:    // JUMPDEST
    PUSH 0x00
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP6
    PUSH 0x84
    MSTORE
    DUP14
    PUSH 0xa4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x44
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L186
    PUSH 0x00
    PUSH 0x00
    REVERT
L186:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L187
    PUSH 0x00
    PUSH 0x00
    REVERT
L187:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L188
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L188:    // JUMPDEST
    DUP6
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    DUP14
    PUSH 0xc0
    MSTORE
    PUSH 0x268d208c45ec3d7213f545c4402b1bc7f11b332757a4e0d84ff4d37b90db1fca    // topic: Swap0for1(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP14
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
L172:    // JUMPDEST
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L3
L204:    // JUMPDEST
    POP
    PUSH 0x44
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L205
    PUSH 0x00
    PUSH 0x00
    REVERT
L205:    // JUMPDEST
    PUSH 0x01
    PUSH 0x00
    TSTORE
    PUSH 0x04
    CALLDATALOAD
    PUSH 0x0100
    MSTORE
    PUSH 0x24
    CALLDATALOAD
    PUSH 0x0100
    MLOAD
    PUSH 0x00
    LT
    JUMPI L206
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L206:    // JUMPDEST
    PUSH 0x02
    SLOAD
    PUSH 0x03
    SLOAD
    DUP2
    PUSH 0x00
    LT
    JUMPI L207
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L207:    // JUMPDEST
    DUP1
    PUSH 0x00
    LT
    JUMPI L208
    PUSH 0xf4560403    // selector: Zero()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L208:    // JUMPDEST
    PUSH 0x07
    SLOAD
    PUSH 0x08
    SLOAD
    PUSH 0x2710
    JUMPI L209
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L209:    // JUMPDEST
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    MUL
    PUSH 0x26f2
    PUSH 0x0100
    MLOAD
    DUP3
    DIV
    EQ
    PUSH 0x0100
    MLOAD
    ISZERO
    OR
    JUMPI L210
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L210:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    DUP5
    ADD
    DUP5
    DUP2
    LT
    ISZERO
    JUMPI L211
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L211:    // JUMPDEST
    DUP1
    JUMPI L212
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L212:    // JUMPDEST
    DUP2
    DUP7
    MUL
    DUP3
    DUP8
    DUP3
    DIV
    EQ
    DUP8
    ISZERO
    OR
    JUMPI L213
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L213:    // JUMPDEST
    DUP2
    DUP2
    DIV
    SWAP1
    POP
    DUP3
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L214
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L214:    // JUMPDEST
    DUP3
    PUSH 0x0100
    MLOAD
    SUB
    PUSH 0x00
    DUP7
    EQ
    DUP1
    PUSH 0x00
    EQ
    JUMPI L216
    POP
    PUSH 0x2710
    JUMPI L232
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L232:    // JUMPDEST
    PUSH 0x00
    DUP2
    MUL
    PUSH 0x00
    DUP3
    DUP3
    DIV
    EQ
    DUP3
    ISZERO
    OR
    JUMPI L233
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L233:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    DUP3
    LT
    ISZERO
    JUMPI L234
    PUSH 0xcd4e6167    // selector: FeeTooHigh()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L234:    // JUMPDEST
    DUP10
    DUP4
    LT
    ISZERO
    JUMPI L235
    PUSH 0xbb2875c3    // selector: InsufficientOutput()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L235:    // JUMPDEST
    DUP3
    PUSH 0x00
    LT
    JUMPI L236
    PUSH 0x1078b533    // selector: ZeroOut()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L236:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L237
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L237:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    DUP1
    DUP10
    ADD
    DUP10
    DUP2
    LT
    ISZERO
    JUMPI L238
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L238:    // JUMPDEST
    DUP1
    PUSH 0x03
    SSTORE
    DUP5
    DUP12
    LT
    ISZERO
    JUMPI L239
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L239:    // JUMPDEST
    DUP5
    DUP12
    SUB
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0a
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L240
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L240:    // JUMPDEST
    DUP1
    PUSH 0x0a
    SSTORE
    CALLER
    ADDRESS
    PUSH 0x01
    SLOAD
    PUSH 0x00
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0x84
    MSTORE
    DUP4
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L241
    PUSH 0x00
    PUSH 0x00
    REVERT
L241:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L242
    PUSH 0x00
    PUSH 0x00
    REVERT
L242:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L243
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L243:    // JUMPDEST
    PUSH 0x00
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP6
    PUSH 0x84
    MSTORE
    DUP14
    PUSH 0xa4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x44
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L244
    PUSH 0x00
    PUSH 0x00
    REVERT
L244:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L245
    PUSH 0x00
    PUSH 0x00
    REVERT
L245:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L246
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L246:    // JUMPDEST
    DUP6
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    DUP14
    PUSH 0xc0
    MSTORE
    PUSH 0xec43a82fae8c251f7aae4f79accf59c765bd798d597ccfd95beef20bf096cc9e    // topic: Swap1for0(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP14
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L215
L216:    // JUMPDEST
    POP
    PUSH 0x2710
    JUMPI L217
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x12
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L217:    // JUMPDEST
    DUP5
    DUP2
    MUL
    DUP6
    DUP3
    DUP3
    DIV
    EQ
    DUP3
    ISZERO
    OR
    JUMPI L218
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L218:    // JUMPDEST
    PUSH 0x2710
    DUP2
    DIV
    SWAP1
    POP
    DUP1
    DUP3
    LT
    ISZERO
    JUMPI L219
    PUSH 0xcd4e6167    // selector: FeeTooHigh()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L219:    // JUMPDEST
    DUP10
    DUP4
    LT
    ISZERO
    JUMPI L220
    PUSH 0xbb2875c3    // selector: InsufficientOutput()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L220:    // JUMPDEST
    DUP3
    PUSH 0x00
    LT
    JUMPI L221
    PUSH 0x1078b533    // selector: ZeroOut()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L221:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    LT
    ISZERO
    JUMPI L222
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L222:    // JUMPDEST
    DUP1
    PUSH 0x0100
    MLOAD
    SUB
    DUP1
    DUP10
    ADD
    DUP10
    DUP2
    LT
    ISZERO
    JUMPI L223
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L223:    // JUMPDEST
    DUP1
    PUSH 0x03
    SSTORE
    DUP5
    DUP12
    LT
    ISZERO
    JUMPI L224
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L224:    // JUMPDEST
    DUP5
    DUP12
    SUB
    DUP1
    PUSH 0x02
    SSTORE
    PUSH 0x0a
    SLOAD
    DUP5
    DUP2
    ADD
    DUP2
    DUP2
    LT
    ISZERO
    JUMPI L225
    PUSH 0x4e487b71
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x11
    PUSH 0x84
    MSTORE
    PUSH 0x24
    PUSH 0x80
    REVERT
L225:    // JUMPDEST
    DUP1
    PUSH 0x0a
    SSTORE
    CALLER
    ADDRESS
    PUSH 0x01
    SLOAD
    PUSH 0x00
    SLOAD
    PUSH 0x00
    PUSH 0x23b872dd
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0x84
    MSTORE
    DUP4
    PUSH 0xa4
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xc4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x64
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L226
    PUSH 0x00
    PUSH 0x00
    REVERT
L226:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L227
    PUSH 0x00
    PUSH 0x00
    REVERT
L227:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L228
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L228:    // JUMPDEST
    PUSH 0x00
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP6
    PUSH 0x84
    MSTORE
    DUP14
    PUSH 0xa4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x44
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L229
    PUSH 0x00
    PUSH 0x00
    REVERT
L229:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L230
    PUSH 0x00
    PUSH 0x00
    REVERT
L230:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L231
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L231:    // JUMPDEST
    DUP6
    PUSH 0x80
    MSTORE
    PUSH 0x0100
    MLOAD
    PUSH 0xa0
    MSTORE
    DUP14
    PUSH 0xc0
    MSTORE
    PUSH 0xec43a82fae8c251f7aae4f79accf59c765bd798d597ccfd95beef20bf096cc9e    // topic: Swap1for0(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP14
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
L215:    // JUMPDEST
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L3
L247:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L248
    PUSH 0x00
    PUSH 0x00
    REVERT
L248:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    CALLER
    PUSH 0x06
    SLOAD
    DUP1
    DUP3
    EQ
    JUMPI L249
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L249:    // JUMPDEST
    DUP3
    PUSH 0x2710
    LT
    ISZERO
    JUMPI L250
    PUSH 0xcd4e6167    // selector: FeeTooHigh()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L250:    // JUMPDEST
    DUP3
    PUSH 0x08
    SSTORE
    DUP3
    PUSH 0x80
    MSTORE
    PUSH 0xac9f8df6116458aab7d2642e648145d5f693b4d6a1f0dff57db25547224c8b55    // topic: ProtocolShareSet(uint256)
    PUSH 0x20
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    POP
    JUMP L3
L251:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L252
    PUSH 0x00
    PUSH 0x00
    REVERT
L252:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    CALLER
    PUSH 0x06
    SLOAD
    DUP1
    DUP3
    EQ
    JUMPI L253
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L253:    // JUMPDEST
    DUP3
    PUSH 0x07
    SSTORE
    DUP3
    PUSH 0x80
    MSTORE
    PUSH 0xe7ba424f407983edfb652af33e51f926d1d41a22bb4850c65eb21c02e378957c    // topic: FeeToSet(address)
    PUSH 0x20
    PUSH 0x80
    LOG1
    STOP
    POP
    POP
    POP
    JUMP L3
L254:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L255
    PUSH 0x00
    PUSH 0x00
    REVERT
L255:    // JUMPDEST
    PUSH 0x01
    PUSH 0x00
    TSTORE
    CALLER
    PUSH 0x07
    SLOAD
    PUSH 0x00
    DUP2
    EQ
    ISZERO
    JUMPI L256
    PUSH 0x6f74ca5d    // selector: NoFeeTo()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L256:    // JUMPDEST
    DUP1
    DUP3
    EQ
    JUMPI L257
    PUSH 0x30cd7471    // selector: NotOwner()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L257:    // JUMPDEST
    PUSH 0x09
    SLOAD
    PUSH 0x0a
    SLOAD
    PUSH 0x00
    PUSH 0x09
    SSTORE
    PUSH 0x00
    PUSH 0x0a
    SSTORE
    PUSH 0x00
    SLOAD
    PUSH 0x01
    SLOAD
    PUSH 0x00
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP7
    PUSH 0x84
    MSTORE
    DUP5
    PUSH 0xa4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x44
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L258
    PUSH 0x00
    PUSH 0x00
    REVERT
L258:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L259
    PUSH 0x00
    PUSH 0x00
    REVERT
L259:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L260
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L260:    // JUMPDEST
    PUSH 0x00
    PUSH 0xa9059cbb
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    DUP8
    PUSH 0x84
    MSTORE
    DUP5
    PUSH 0xa4
    MSTORE
    PUSH 0x20
    PUSH 0x80
    PUSH 0x44
    PUSH 0x80
    PUSH 0x00
    DUP8
    PUSH 0x0f4240
    CALL
    DUP1
    JUMPI L261
    PUSH 0x00
    PUSH 0x00
    REVERT
L261:    // JUMPDEST
    PUSH 0x40
    RETURNDATASIZE
    LT
    PUSH 0x20
    RETURNDATASIZE
    LT
    ISZERO
    AND
    RETURNDATASIZE
    ISZERO
    OR
    JUMPI L262
    PUSH 0x00
    PUSH 0x00
    REVERT
L262:    // JUMPDEST
    PUSH 0x80
    MLOAD
    ISZERO
    ISZERO
    RETURNDATASIZE
    ISZERO
    OR
    SWAP2
    POP
    POP
    PUSH 0x01
    DUP2
    EQ
    JUMPI L263
    PUSH 0x90b8ec18    // selector: TransferFailed()
    PUSH 0xe0
    SHL
    PUSH 0x80
    MSTORE
    PUSH 0x04
    PUSH 0x80
    REVERT
L263:    // JUMPDEST
    DUP8
    PUSH 0x80
    MSTORE
    DUP6
    PUSH 0xa0
    MSTORE
    DUP5
    PUSH 0xc0
    MSTORE
    PUSH 0xd24ccccf373129a9579bb9f5edc41c09218d54ae950e90b4d5ca2927b7c29b11    // topic: ProtocolFeesCollected(address,uint256,uint256)
    PUSH 0x60
    PUSH 0x80
    LOG1
    PUSH 0x00
    PUSH 0x00
    TSTORE
    DUP6
    PUSH 0x80
    MSTORE
    DUP5
    PUSH 0xa0
    MSTORE
    PUSH 0x40
    PUSH 0x80
    RETURN
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    POP
    JUMP L3
L264:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L265
    PUSH 0x00
    PUSH 0x00
    REVERT
L265:    // JUMPDEST
    PUSH 0x02
    SLOAD
    PUSH 0x03
    SLOAD
    DUP2
    PUSH 0x80
    MSTORE
    DUP1
    PUSH 0xa0
    MSTORE
    PUSH 0x40
    PUSH 0x80
    RETURN
    POP
    POP
    JUMP L3
L266:    // JUMPDEST
    POP
    PUSH 0x24
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L267
    PUSH 0x00
    PUSH 0x00
    REVERT
L267:    // JUMPDEST
    PUSH 0x04
    CALLDATALOAD
    DUP1
    PUSH 0x00
    MSTORE
    PUSH 0x05
    PUSH 0x20
    MSTORE
    PUSH 0x40
    PUSH 0x00
    KECCAK256
    SLOAD
    DUP1
    PUSH 0x80
    MSTORE
    PUSH 0x20
    PUSH 0x80
    RETURN
    POP
    POP
    JUMP L3
L268:    // JUMPDEST
    POP
    PUSH 0x04
    CALLDATASIZE
    LT
    ISZERO
    JUMPI L269
    PUSH 0x00
    PUSH 0x00
    REVERT
L269:    // JUMPDEST
    PUSH 0x09
    SLOAD
    PUSH 0x0a
    SLOAD
    DUP2
    PUSH 0x80
    MSTORE
    DUP1
    PUSH 0xa0
    MSTORE
    PUSH 0x40
    PUSH 0x80
    RETURN
    POP
    POP
L3:    // JUMPDEST
