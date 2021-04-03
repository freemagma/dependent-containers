module Data.Binary

import Data.Primitives.Views

%access public export

data Bin = MSEnd | B0 Bin | B1 Bin

succ : Bin -> Bin
succ MSEnd = B1 MSEnd
succ (B0 b) = B1 b
succ (B1 b) = B0 $ succ b

total
plus : Bin -> Bin -> Bin
plus b MSEnd = b
plus MSEnd b = b
plus (B0 a) (B0 b) = B0 $ plus a b
plus (B0 a) (B1 b) = B1 $ plus a b
plus (B1 a) (B0 b) = B1 $ plus a b
plus (B1 a) (B1 b) = B0 . succ $ plus a b

(>>) : Bin -> Nat -> Bin
b >> Z = b
b >> (S n) = B0 $ b >> n

mult : Bin -> Bin -> Bin
mult MSEnd _ = MSEnd
mult _ MSEnd = MSEnd
mult (B0 b) x = (mult b x) >> 1
mult (B1 b) x = plus x $ (mult b x) >> 1 

data Parity = Even | Odd

fastHalf : Integer -> Integer
fastHalf n with (divides n 2)
  fastHalf ((2 * div) + _) | DivBy _ = div

fastHalfMod : Integer -> Integer
fastHalfMod n with (divides n 2)
  fastHalfMod ((2 * _) + rem) | DivBy _ = rem

integerParity : Integer -> Parity
integerParity n =
  -- abs is not necessary since we're checking on 0 or _
  -- without abs, _ can be 1 or -1
  let remainder = fastHalfMod n in
    if remainder == 0
      then Even
      else Odd

fromNat : Nat -> Bin
fromNat Z = MSEnd
fromNat (S k) = succ $ fromNat k 

mutual
  fromIntegerBinHelp : Integer -> Parity -> Bin
  fromIntegerBinHelp x Even = B0 (fromIntegerBin x)
  fromIntegerBinHelp x Odd  = B1 (fromIntegerBin x)

  fromIntegerBin : Integer -> Bin
  fromIntegerBin n =
    if n > 0
      -- quotient' is < n because fastHalf n floors
      then let quotient = fastHalf n
               quotient' = assert_smaller n quotient in
             fromIntegerBinHelp quotient' (integerParity n)
      else MSEnd

toIntegerBin : Bin -> Integer
toIntegerBin MSEnd = 0
toIntegerBin (B0 b) = 2 * (toIntegerBin b)
toIntegerBin (B1 b) = 1 + 2 * (toIntegerBin b)

-------------------------------
-- Interface implementations 
-------------------------------

-- Eq Bin where
--     MSEnd == MSEnd   = True
--     (B0 a) == (B0 b) = a == b
--     (B1 a) == (B1 b) = a == b
--     _ == _           = False

Cast Bin Integer where
    cast = toIntegerBin

Num Bin where
    (+) = plus
    (*) = mult
    fromInteger = fromIntegerBin

Abs Bin where
    abs = id

Cast Integer Bin where
    cast = fromInteger

Cast String Bin where
    cast str = cast (the Integer (cast str))

Cast Bin String where
    cast n = cast (the Integer (cast n))

-------------------------------
-- Proofs
-------------------------------

plusMSEndLeftIdentity : (b : Bin) -> plus MSEnd b = b
plusMSEndLeftIdentity MSEnd = Refl
plusMSEndLeftIdentity (B0 b) = Refl
plusMSEndLeftIdentity (B1 b) = Refl

succIsOnePlus : (b : Bin) -> plus (B1 MSEnd) b = succ b
succIsOnePlus MSEnd = Refl
succIsOnePlus (B0 b) = rewrite plusMSEndLeftIdentity b in Refl
succIsOnePlus (B1 b) = rewrite plusMSEndLeftIdentity b in Refl



