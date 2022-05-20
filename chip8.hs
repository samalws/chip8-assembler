{-# LANGUAGE GeneralizedNewtypeDeriving, RecursiveDo, BinaryLiterals #-}
-- note: mdo magically works even if we have Asm IO ()

import Prelude hiding (writeFile)
import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.State (StateT, evalStateT, modify, get)
import Control.Monad.Writer (WriterT, execWriterT, tell)
import Data.ByteString (ByteString, pack, writeFile)
import Data.Functor.Identity (runIdentity)
import Data.Word (Word8, Word16)
-- import Control.Monad.IO.Class (liftIO)

fromBinaryList [] = 0
fromBinaryList l = (fromBinaryList (init l)) * 2 + last l

data Nybble = N0 | N1 | N2 | N3 | N4 | N5 | N6 | N7 | N8 | N9 | NA | NB | NC | ND | NE | NF deriving (Read, Show, Eq, Ord, Enum)
newtype Reg = Reg { fromReg :: Nybble } deriving (Read, Show, Eq, Ord, Enum)
newtype Lbl = Lbl { fromLbl :: Word16 } deriving (Read, Show, Eq, Ord, Enum, Num, Bounded)
type Asm m a = WriterT ByteString (StateT Lbl m) a

r0 = Reg N0
r1 = Reg N1
r2 = Reg N2
r3 = Reg N3
r4 = Reg N4
r5 = Reg N5
r6 = Reg N6
r7 = Reg N7
r8 = Reg N8
r9 = Reg N9
rA = Reg NA
rB = Reg NB
rC = Reg NC
rD = Reg ND
rE = Reg NE
rF = Reg NF

constructWord8 (a,b) = toEnum (fromEnum a * (2^4) + fromEnum b)
decomp2 _nn = (toEnum $ nn `div` (2^4), toEnum $ nn `mod` (2^4)) :: (Nybble, Nybble) where
  nn = fromEnum _nn
decomp3 _nnn = (a,b, toEnum (nnn `mod` (2^4)) :: Nybble) where
  nnn = fromEnum _nnn
  (a,b) = decomp2 (nnn `div` (2^4))

raw :: (Monad m) => [Word8] -> Asm m ()
raw a = tell (pack a) >> modify (+ toEnum (length a))

opcode :: (Monad m, Enum a, Enum b, Enum c, Enum d) => (a,b,c,d) -> Asm m ()
opcode (a,b,c,d) = raw [constructWord8 (a,b), constructWord8 (c,d)]

label :: (Monad m) => Asm m Lbl
label = get

lit8 :: Word8 -> Word8
lit8 = id

-- OPCODES

jmp     nnn@(Lbl{}) = opcode (1,   a,b,c) where (a,b,c) = decomp3 nnn
jmpPlus nnn@(Lbl{}) = opcode (0xB, a,b,c) where (a,b,c) = decomp3 nnn
call    nnn@(Lbl{}) = opcode (2,   a,b,c) where (a,b,c) = decomp3 nnn

setI   nnn@(Lbl{}) = opcode (0xA, a,b,c) where (a,b,c) = decomp3 nnn
addI   x@(Reg{})   = opcode (0xF, x, 1, 0xE)
readI  x@(Reg{})   = opcode (0xF, x, 6, 5)
writeI x@(Reg{})   = opcode (0xF, x, 5, 5)

ret :: (Monad m) => Asm m ()
ret = opcode (0,0,0xE,0xE)

or'  x@(Reg{}) y@(Reg{}) = opcode (8,x,y,1)
and' x@(Reg{}) y@(Reg{}) = opcode (8,x,y,2)
xor  x@(Reg{}) y@(Reg{}) = opcode (8,x,y,3)
sub  x@(Reg{}) y@(Reg{}) = opcode (8,x,y,5)
subn x@(Reg{}) y@(Reg{}) = opcode (8,x,y,7)
shr  x@(Reg{}) y@(Reg{}) = opcode (8,x,y,6)
shl  x@(Reg{}) y@(Reg{}) = opcode (8,x,y,0xE)

rnd x@(Reg{}) nn = opcode (0xC, x, a,b) where (a,b) = decomp2 nn
bcd x@(Reg{}) = opcode (0xF, x, 3,3)

clearScreen :: (Monad m) => Asm m ()
clearScreen = opcode (0,0,0xE,0)
draw x@(Reg{}) y@(Reg{}) n = opcode (0xD,x,y,n)
hex x@(Reg{}) = opcode (0xF,x,2,9)

skipKeypad x@(Reg{}) = opcode (0xE,x,9,0xE)
skipNotKeypad x@(Reg{}) = opcode (0xE,x,0xA,1)
waitKeypad x@(Reg{}) = opcode (0xF,x,0,0xA)

readDelay  x@(Reg{}) = opcode (0xF, x, 0,7)
writeDelay x@(Reg{}) = opcode (0xF, x, 1,5)
writeSound x@(Reg{}) = opcode (0xF, x, 1,8)

class RegOrWord8 a where
  skipEq  :: (Monad m) => Reg -> a -> Asm m ()
  skipNeq :: (Monad m) => Reg -> a -> Asm m ()
  mov     :: (Monad m) => Reg -> a -> Asm m ()
  add     :: (Monad m) => Reg -> a -> Asm m ()

instance RegOrWord8 Reg where
  skipEq  x y = opcode (5,x,y,0)
  skipNeq x y = opcode (9,x,y,0)
  mov     x y = opcode (8,x,y,0)
  add     x y = opcode (8,x,y,4)

instance RegOrWord8 Word8 where
  skipEq  x nn = opcode (3,x,a,b) where (a,b) = decomp2 nn
  skipNeq x nn = opcode (4,x,a,b) where (a,b) = decomp2 nn
  mov     x nn = opcode (6,x,a,b) where (a,b) = decomp2 nn
  add     x nn = opcode (7,x,a,b) where (a,b) = decomp2 nn

infixl 1 +=
infixl 1 <--
infixl 1 &=
infixl 1 |=
infixl 1 ^=
infixl 1 -=
infixl 1 =-
infixl 1 >>>=
infixl 1 <<<=

(+=)   :: (RegOrWord8 a, Monad m) => Reg -> a -> Asm m ()
(+=)   = add
(<--)  :: (RegOrWord8 a, Monad m) => Reg -> a -> Asm m ()
(<--)  = mov
(&=)   :: (Monad m) => Reg -> Reg -> Asm m ()
(&=)   = and'
(|=)   :: (Monad m) => Reg -> Reg -> Asm m ()
(|=)   = or'
(^=)   :: (Monad m) => Reg -> Reg -> Asm m ()
(^=)   = xor
(-=)   :: (Monad m) => Reg -> Reg -> Asm m ()
(-=)   = sub
(=-)   :: (Monad m) => Reg -> Reg -> Asm m ()
(=-)   = subn
(>>>=) :: (Monad m) => Reg -> Reg -> Asm m ()
(>>>=) = shr
(<<<=) :: (Monad m) => Reg -> Reg -> Asm m ()
(<<<=) = shl

-- MULTI-OPCODE BASIC MINI-FUNCTIONS

infiniteLoop :: (Monad m) => Asm m ()
infiniteLoop = label >>= jmp

jmpEq a b lbl = do
  skipNeq a b
  jmp lbl

jmpNeq a b lbl = do
  skipEq a b
  jmp lbl

inc a = a += lit8 1
dec a = a += lit8 maxBound

-- calculate a * b, storing result in c
-- clobbers a and F
-- a, b, and c must be distinct
-- a and c must be registers
-- b must be either a register or a Word8
mul a b c = mdo
  beginning <- label
  jmpEq a (lit8 0) end
  c += b
  dec a
  jmp beginning
  end <- label
  pure ()

-- calculate a / b and a % b, storing results in c and a respectively
-- if c is Nothing, ignores a / b result
-- if getMod is False, ignores a % b result
-- clobbers a, c, and F
-- a, b, and c must be distinct registers (c can also be Nothing)
-- d must be a boolean
divAndMod a b c getMod = do
  mapM_ (<-- lit8 0) c
  beginning <- label
  a -= b
  mapM_ inc c
  jmpEq rF (lit8 0) beginning
  mapM_ dec c
  when getMod (a += b)
  pure ()

-- EXAMPLE PROGRAMS

exampleProgram :: (MonadFix m) => Asm m ()
exampleProgram = do
  r1 <-- lit8 5
  r1 += r1
  r2 <-- lit8 3
  mul r1 r2 r3
  r1 <-- lit8 2
  divAndMod r3 r1 (Just r4) True
  infiniteLoop

drawStuffProgram :: (MonadFix m) => Asm m ()
drawStuffProgram = mdo
  clearScreen
  r1 <-- lit8 0
  r2 <-- lit8 0
  r3 <-- lit8 0
  hex r3
  draw r1 r2 (lit8 5)
  r1 += (lit8 5)
  draw r1 r2 (lit8 5)
  r1 += (lit8 5)
  setI funnySprite
  draw r1 r2 (lit8 5)
  r1 += (lit8 9)
  setI amogusSprite
  draw r1 r2 (lit8 8)
  infiniteLoop
  funnySprite <- label
  raw [0b10001000]
  raw [0b00000000]
  raw [0b10000001]
  raw [0b01000010]
  raw [0b00111100]
  amogusSprite <- label
  raw [0b01111100]
  raw [0b11000110]
  raw [0b11000111]
  raw [0b11111111]
  raw [0b11111111]
  raw [0b11111110]
  raw [0b11000110]
  raw [0b11000110]

fromSevenSeg (a,b,c,d,e,f,g) = do
  raw' [q,a,a,r]
  raw' [f,0,0,b]
  raw' [f,0,0,b]
  raw' [s,g,g,t]
  raw' [e,0,0,c]
  raw' [e,0,0,c]
  raw' [u,d,d,v]
  where
    raw' l = raw [fromBinaryList (l <> [0,0,0,0])]
    q = _or a f
    r = _or a b
    s = _or g (_or e f)
    t = _or g (_or a b)
    u = _or d e
    v = _or c d
    _or 0 0 = 0
    _or _ _ = 1

allSevenSegNumbers :: (Monad m) => Asm m [Lbl]
allSevenSegNumbers = mapM (\l -> label <* fromSevenSeg l) [
    (1,1,1,1,1,1,0), -- 0
    (0,1,1,0,0,0,0), -- 1
    (1,1,0,1,1,0,1), -- 2
    (1,1,1,1,0,0,1), -- 3
    (0,1,1,0,0,1,1), -- 4
    (1,0,1,1,0,1,1), -- 5
    (1,0,1,1,1,1,1), -- 6
    (1,1,1,0,0,0,0), -- 7
    (1,1,1,1,1,1,1), -- 8
    (1,1,1,0,0,1,1), -- 9
    (1,1,1,0,1,1,1), -- A
    (0,0,1,1,1,1,1), -- b
    (1,0,0,1,1,1,0), -- C
    (0,1,1,1,1,0,1), -- d
    (1,0,0,1,1,1,1), -- E
    (1,0,0,0,1,1,1)  -- F
  ]

drawSevenSegNumber :: (Monad m) => [Lbl] -> Reg -> Reg -> Reg -> Asm m ()
drawSevenSegNumber nums rx ry rn = do
  sequence [skipNeq rn (lit8 n) >> setI (nums !! (fromEnum n)) | n <- [0..0xF]]
  draw rx ry (lit8 7)
  rx += lit8 5

program = mdo
  clearScreen
  r5 <-- lit8 2
  r6 <-- lit8 4
  mul r5 r6 r0
  r2 <-- lit8 0
  r3 <-- lit8 0
  drawSevenSegNumber nums r2 r3 r0
  drawSevenSegNumber nums r2 r3 r0
  hex r0
  draw r2 r3 (lit8 5)
  infiniteLoop
  nums <- allSevenSegNumbers
  pure ()

compile = runIdentity . flip evalStateT 0x200 . execWriterT

main = writeFile "otp.chip8" (compile program)
