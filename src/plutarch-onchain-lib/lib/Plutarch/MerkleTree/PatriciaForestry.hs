{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE OverloadedRecordDot     #-}
{-# LANGUAGE OverloadedStrings       #-}
{-# LANGUAGE PartialTypeSignatures   #-}
{-# LANGUAGE TemplateHaskell         #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE InstanceSigs            #-}
{-# LANGUAGE NamedFieldPuns          #-}
{-|
Module      : Plutarch.MerkleTree.PatriciaForestry
Description : Merkle trees in Plutarch
Copyright   : (c) Philip DiSarro, 2024
Stability   : experimental

-}
module Plutarch.MerkleTree.PatriciaForestry(
  pblake2b_256_digest_size,
  MerklePatriciaForestry(..),
  PMerklePatriciaForestry(..),
  pfrom_root,
  pempty,
  pis_empty,

  -- * Proofs
  Neighbor(..),
  ProofStep(..),
  PNeighbor(..),
  PProofStep(..),
  PProof(..),

  pinsert,
  pdelete,
  pupdate,
  phas,
  pexcluding,
  pincluding,
  pdo_branch,
  pdo_fork
) where

import Data.ByteString (ByteString)
import Generics.SOP qualified as SOP
import GHC.Generics (Generic)
import Plutarch.Builtin.Crypto (pblake2b_256)
import Plutarch.Core.Internal.Builtins (pconsBS')
import Plutarch.Internal.Lift
import Plutarch.MerkleTree.Helpers (pcombine, pnibble, pnibbles, psuffix)
import Plutarch.MerkleTree.Merkling (pmerkle_16, pnull_hash, psparse_merkle_16)
import Plutarch.Prelude
import Plutarch.Repr.Data
import PlutusTx qualified
import PlutusTx.Builtins as Builtins
import PlutusTx.Builtins.Internal (BuiltinByteString (BuiltinByteString))
import PlutusTx.Builtins.Internal qualified as BI

-- Constants

pblake2b_256_digest_size :: Term s PInteger
pblake2b_256_digest_size = pconstant 32

-- Merkle Patricia Forestry

newtype MerklePatriciaForestry = MerklePatriciaForestry BuiltinByteString
  deriving stock (Show, Eq, Ord, Generic)
PlutusTx.unstableMakeIsData ''MerklePatriciaForestry
PlutusTx.makeLift ''MerklePatriciaForestry

newtype PMerklePatriciaForestry (s :: S) = PMerklePatriciaForestry (Term s PByteString)
  deriving stock (Generic)
  deriving anyclass (SOP.Generic, PIsData, POrd, PEq, PShow)
  deriving
    ( PlutusType )
    via (DeriveNewtypePlutusType PMerklePatriciaForestry)

instance PLiftable PMerklePatriciaForestry where
  type AsHaskell PMerklePatriciaForestry = MerklePatriciaForestry
  type PlutusRepr PMerklePatriciaForestry = ByteString
  {-# INLINEABLE haskToRepr #-}
  haskToRepr :: AsHaskell PMerklePatriciaForestry -> PlutusRepr PMerklePatriciaForestry
  haskToRepr (MerklePatriciaForestry (BuiltinByteString str)) = str
  {-# INLINEABLE reprToHask #-}
  reprToHask :: PlutusRepr PMerklePatriciaForestry -> Either LiftError (AsHaskell PMerklePatriciaForestry)
  reprToHask = Right . MerklePatriciaForestry . BuiltinByteString
  {-# INLINEABLE reprToPlut #-}
  reprToPlut :: PlutusRepr PMerklePatriciaForestry -> PLifted s PMerklePatriciaForestry
  reprToPlut = reprToPlutUni
  {-# INLINEABLE plutToRepr #-}
  plutToRepr :: (forall (s :: S). PLifted s PMerklePatriciaForestry) -> Either LiftError (PlutusRepr PMerklePatriciaForestry)
  plutToRepr = plutToReprUni

pfrom_root :: Term s (PByteString :--> PMerklePatriciaForestry)
pfrom_root = phoistAcyclic $ plam $ \root_ ->
  pif (plengthBS # root_ #== pblake2b_256_digest_size)
    (pcon $ PMerklePatriciaForestry root_)
    perror

pempty :: Term s PMerklePatriciaForestry
pempty = pcon $ PMerklePatriciaForestry pnull_hash

pis_empty :: Term s (PMerklePatriciaForestry :--> PBool)
pis_empty = phoistAcyclic $ plam $ \self ->
  pmatch self $ \(PMerklePatriciaForestry root_) ->
    root_ #== pnull_hash

data Neighbor = Neighbor
  { nibble :: Integer
  , prefix :: BuiltinByteString
  , root   :: BuiltinByteString
  }
  deriving stock (Show, Eq, Generic)

instance PlutusTx.ToData Neighbor where
  {-# INLINABLE toBuiltinData #-}
  toBuiltinData :: Neighbor -> PlutusTx.BuiltinData
  toBuiltinData (Neighbor{nibble, prefix, root}) = PlutusTx.toBuiltinData [PlutusTx.toBuiltinData nibble, PlutusTx.toBuiltinData prefix, PlutusTx.toBuiltinData root]

instance PlutusTx.FromData Neighbor where
  {-# INLINABLE fromBuiltinData #-}
  fromBuiltinData :: PlutusTx.BuiltinData -> Maybe Neighbor
  fromBuiltinData neighbor =
    let toNeighbor :: BI.BuiltinData -> Maybe Neighbor
        toNeighbor neighborList' = do
          let neighborList = BI.unsafeDataAsList neighborList'
          nibble <- PlutusTx.fromBuiltinData $ BI.head neighborList
          prefix <- PlutusTx.fromBuiltinData $ BI.head (BI.tail neighborList)
          root <- PlutusTx.fromBuiltinData $ BI.head (BI.tail $ BI.tail neighborList)
          return Neighbor{nibble, prefix, root}
    in
      BI.chooseData neighbor
          Nothing
          Nothing
          (toNeighbor neighbor)
          Nothing
          Nothing

instance PlutusTx.UnsafeFromData Neighbor where
  {-# INLINABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData :: PlutusTx.BuiltinData -> Neighbor
  unsafeFromBuiltinData neighbor =
    let bd = BI.unsafeDataAsList neighbor
        nibble = PlutusTx.unsafeFromBuiltinData $ BI.head bd
        prefix = PlutusTx.unsafeFromBuiltinData $ BI.head $ BI.tail bd
        root = PlutusTx.unsafeFromBuiltinData $ BI.head $ BI.tail $ BI.tail bd
    in Neighbor{nibble, prefix, root}

data ProofStep
  = Branch
      { skip      :: Integer
      , neighbors :: BuiltinByteString
      }
  | Fork
      { skip     :: Integer
      , neighbor :: Neighbor
      }
  | Leaf
      { skip  :: Integer
      , key   :: BuiltinByteString
      , value :: BuiltinByteString
      }
  deriving stock (Show, Eq, Generic)
PlutusTx.unstableMakeIsData ''ProofStep

data PProofStep (s :: S)
 = PBranch
    { pproofStep'skip :: Term s (PAsData PInteger)
    , pproofStep'neighbors :: Term s (PAsData PByteString)
    }
  | PFork
      { pproofStep'skip :: Term s (PAsData PInteger)
      , pproofStep'neighbor :: Term s (PAsData PNeighbor)
      }
  | PLeaf
      { pproofStep'skip :: Term s (PAsData PInteger)
      , pproofStep'key :: Term s (PAsData PByteString)
      , pproofStep'value :: Term s (PAsData PByteString)
      }
  deriving stock (Generic)
  deriving anyclass (SOP.Generic, PIsData, PShow, PEq)
  deriving (PlutusType) via (DeriveAsDataStruct PProofStep)

deriving via
  DeriveDataPLiftable PProofStep ProofStep
  instance
    PLiftable PProofStep

newtype PProof (s :: S) = PProof (Term s (PBuiltinList (PAsData PProofStep)))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PProof where type DPTStrat _ = PlutusTypeNewtype

data PNeighbor (s :: S) = PNeighbor
  { pneighbor'nibble :: Term s (PAsData PInteger)
  , pneighbor'prefix :: Term s (PAsData PByteString)
  , pneighbor'root :: Term s (PAsData PByteString)
  }
  deriving stock (Generic)
  deriving anyclass (SOP.Generic, PIsData, PEq, PShow)
  deriving (PlutusType) via (DeriveAsDataRec PNeighbor)


deriving via
  DeriveDataPLiftable (PAsData PNeighbor) Neighbor
  instance
    PLiftable PNeighbor

-- Test whether an element is present in the trie with a specific value. This
-- requires a Proof of inclusion for the element. The latter can be
-- obtained off-chain from the whole trie containing the element.
--
-- Returns `False` when the element isn't in the tree.
phas :: Term s (PMerklePatriciaForestry :--> PByteString :--> PByteString :--> PProof :--> PBool)
phas = phoistAcyclic $ plam $ \self key_ value_ proof ->
  pmatch self $ \(PMerklePatriciaForestry root_) ->
    pincluding # key_ # value_ # proof #== root_

-- Insert an element in the trie. This requires a [Proof](#Proof) of inclusion
-- for the element. The latter can be obtained off-chain from the whole trie
-- containing the element.
--
-- #### Fails when
--
-- - The Proof is invalid.
-- - There's already an element in the trie at the given key.
pinsert :: Term s (PMerklePatriciaForestry :--> PByteString :--> PByteString :--> PProof :--> PMerklePatriciaForestry)
pinsert = phoistAcyclic $ plam $ \self key_ value_ proof ->
  pmatch self $ \(PMerklePatriciaForestry root_) ->
    pif
      ((pexcluding # key_ # proof) #== root_)
      (pcon $ PMerklePatriciaForestry (pincluding # key_ # value_ # proof))
      perror

pdelete :: Term s (PMerklePatriciaForestry :--> PByteString :--> PByteString :--> PProof :--> PMerklePatriciaForestry)
pdelete = phoistAcyclic $ plam $ \self key_ value_ proof_ ->
  pif
    ((pincluding # key_ # value_ # proof_) #== pto self)
    (pcon $ PMerklePatriciaForestry (pexcluding # key_ # proof_))
    perror

pupdate :: Term s (PMerklePatriciaForestry :--> PByteString :--> PProof :--> PByteString :--> PByteString :--> PMerklePatriciaForestry)
pupdate = phoistAcyclic $ plam $ \self key_ proof oldValue newValue ->
  pif
    ((pincluding # key_ # oldValue # proof) #== pto self)
    (pcon $ PMerklePatriciaForestry (pincluding # key_ # newValue # proof))
    perror

pexcluding :: Term s (PByteString  :--> PProof :--> PByteString)
pexcluding = phoistAcyclic $ plam $ \((pblake2b_256 #) -> path) proof ->
  let go :: Term _ (PInteger :--> PBuiltinList (PAsData PProofStep) :--> PByteString)
      go = pfix #$ plam $ \self cursor steps ->
        pmatch steps $ \case
          PNil -> pnull_hash
          PCons x xs ->
            pmatch (pfromData x) $ \case
              PBranch {pproofStep'skip, pproofStep'neighbors} ->
                plet (cursor + 1 + pfromData pproofStep'skip) $ \nextCursor ->
                  let root_ = (self # nextCursor # xs)
                  in pdo_branch # path # cursor # nextCursor # root_ # pfromData pproofStep'neighbors
              PFork {pproofStep'skip, pproofStep'neighbor} ->
                pmatch xs $ \case
                  PNil ->
                    pmatch (pfromData pproofStep'neighbor) $ \(PNeighbor {pneighbor'nibble, pneighbor'prefix, pneighbor'root}) ->
                      let prefix_ = pconsBS' # pfromData pneighbor'nibble # pfromData pneighbor'prefix
                      in pcombine # prefix_ # pfromData pneighbor'root
                  PCons _ _ ->
                    plet (cursor + 1 + pfromData pproofStep'skip) $ \nextCursor ->
                      let root_ = (self # nextCursor # xs)
                      in pdo_fork # path # cursor # nextCursor # root_ # pfromData pproofStep'neighbor
              PLeaf {pproofStep'skip, pproofStep'key, pproofStep'value} ->
                pmatch xs $ \case
                  PNil ->
                    pcombine # (psuffix # pfromData pproofStep'key # cursor) # pfromData pproofStep'value
                  PCons _ _ ->
                    plet (cursor + 1 + pfromData pproofStep'skip) $ \nextCursor ->
                    plet (pfromData pproofStep'key) $ \leafKey ->
                    let root_ = (self # nextCursor # xs)
                        neighbor_ = pcon $
                          PNeighbor {
                            pneighbor'nibble = pdata (pnibble # leafKey # cursor),
                            pneighbor'prefix = pdata (psuffix # leafKey # nextCursor),
                            pneighbor'root = pproofStep'value
                          }
                      in pdo_fork # path # cursor # nextCursor # root_ # neighbor_
  in go # 0 # pto proof

-- | Compute the resulting hash digest from a 'Proof' associated with an
-- arbitrary value. If the proof is valid, the result is the root hash of
-- the target trie.
--
-- This can be used to check for membership of an element in a trie.
--
pincluding :: Term s (PByteString :--> PByteString :--> PProof :--> PByteString)
pincluding = phoistAcyclic $ plam $ \((pblake2b_256 #) -> path) ((pblake2b_256 #) -> value_) proof ->
  let go :: Term _ (PInteger :--> PBuiltinList (PAsData PProofStep) :--> PByteString)
      go = pfix #$ plam $ \self cursor steps ->
        pelimList (\proofStep ys ->
          pmatch (pfromData proofStep) $ \case
            PBranch {pproofStep'skip, pproofStep'neighbors} ->
              plet (cursor + 1 + pfromData pproofStep'skip) $ \nextCursor ->
                let root_ = self # nextCursor # ys
                in pdo_branch # path # cursor # nextCursor # root_ # pfromData pproofStep'neighbors
            PFork {pproofStep'skip, pproofStep'neighbor} ->
              plet (cursor + 1 + pfromData pproofStep'skip) $ \nextCursor ->
                let root_ = self # nextCursor # ys
                in pdo_fork # path # cursor # nextCursor # root_ # pfromData pproofStep'neighbor
            PLeaf {pproofStep'skip, pproofStep'key, pproofStep'value} ->
              plet (cursor + 1 + pfromData pproofStep'skip) $ \nextCursor ->
                plet pproofStep'key $ \key_ ->
                  let neighbor_ = pcon $
                        PNeighbor {
                          pneighbor'nibble = pdata (pnibble # pfromData key_ # (nextCursor - 1)),
                          pneighbor'prefix = pdata (psuffix # pfromData key_ # nextCursor),
                          pneighbor'root = pproofStep'value
                        }
                      root_ = self # nextCursor # ys
                  in pdo_fork # path # cursor # nextCursor # root_ # neighbor_

        )
        (pcombine # (psuffix # path # cursor) # value_)
        steps
   in go # 0 # pto proof

pdo_branch :: Term s (PByteString :--> PInteger :--> PInteger :--> PByteString :--> PByteString :--> PByteString)
pdo_branch = phoistAcyclic $ plam $ \path cursor nextCursor root_ neighbors_ ->
  plet (pnibble # path # (nextCursor - 1)) $ \branch ->
  plet (pnibbles # path # cursor # (nextCursor - 1)) $ \prefix_ ->
  pcombine # prefix_ #
    (pmerkle_16 # branch # root_
      # (psliceBS # 0 # pblake2b_256_digest_size # neighbors_)
      # (psliceBS # 32 # pblake2b_256_digest_size # neighbors_)
      # (psliceBS # 64 # pblake2b_256_digest_size # neighbors_)
      # (psliceBS # 96 # pblake2b_256_digest_size # neighbors_))

pdo_fork :: Term s (PByteString :--> PInteger :--> PInteger :--> PByteString :--> PNeighbor :--> PByteString)
pdo_fork = phoistAcyclic $ plam $ \path cursor nextCursor root_ neighbor_ ->
  pmatch neighbor_ $ \PNeighbor {pneighbor'nibble, pneighbor'prefix, pneighbor'root} ->
  plet (pnibble # path # (nextCursor - 1)) $ \branch ->
  plet (pnibbles # path # cursor # (nextCursor - 1)) $ \prefix_ ->
  plet (pfromData pneighbor'nibble) $ \neighborNibble ->
  pif (branch #== neighborNibble)
    perror
    (pcombine # prefix_ #
      (psparse_merkle_16 # branch # root_ #
        neighborNibble #
        (pcombine # pfromData pneighbor'prefix # pfromData pneighbor'root)))
