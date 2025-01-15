{-# LANGUAGE OverloadedRecordDot   #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
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

import           Plutarch.Builtin.Crypto      (pblake2b_256)
import           Plutarch.DataRepr
import           Plutarch.Internal.Lift
import           Plutarch.Core.Internal.Builtins          (pconsBS')
import           Plutarch.MerkleTree.Helpers  (pcombine, pnibble, pnibbles,
                                               psuffix)
import           Plutarch.MerkleTree.Merkling (pmerkle_16, pnull_hash,
                                               psparse_merkle_16)
import           Plutarch.Prelude
import PlutusTx.Builtins.Internal (BuiltinByteString (BuiltinByteString))
--import           PlutusLedgerApi.V2           (BuiltinByteString)
import           GHC.Generics (Generic)
import qualified PlutusTx

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
  deriving anyclass (PlutusType, PIsData, PEq, PShow)

instance DerivePlutusType PMerklePatriciaForestry where type DPTStrat _ = PlutusTypeNewtype

-- instance
--   PLiftable PMerklePatriciaForestry
--   where
--   type AsHaskell PMerklePatriciaForestry = BuiltinByteString
--   type PlutusRepr PMerklePatriciaForestry = PLiftedClosed PMerklePatriciaForestry

instance {-# OVERLAPPING #-} PLiftable PMerklePatriciaForestry where
  type AsHaskell PMerklePatriciaForestry = AsHaskell PByteString
  type PlutusRepr PMerklePatriciaForestry = PlutusTx.Data
  {-# INLINEABLE toPlutarchRepr #-}
  toPlutarchRepr = PlutusTx.toData . BuiltinByteString
  {-# INLINEABLE toPlutarch #-}
  toPlutarch = toPlutarchUni
  {-# INLINEABLE fromPlutarchRepr #-}
  fromPlutarchRepr x = (\(BuiltinByteString str) -> str) <$> PlutusTx.fromData x
  {-# INLINEABLE fromPlutarch #-}
  fromPlutarch = fromPlutarchUni

-- deriving via
--   DeriveDataPLiftable PMerklePatriciaForestry MerklePatriciaForestry
--   instance
--     PLiftable PMerklePatriciaForestry

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
PlutusTx.unstableMakeIsData ''Neighbor

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
  = PBranch (Term s (PDataRecord '["skip" ':= PInteger, "neighbors" ':= PByteString]))
  | PFork (Term s (PDataRecord '["skip" ':= PInteger, "neighbor" ':= PNeighbor]))
  | PLeaf (Term s (PDataRecord '["skip" ':= PInteger, "key" ':= PByteString, "value" ':= PByteString]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PProofStep where type DPTStrat _ = PlutusTypeData

deriving via
  DeriveDataPLiftable PProofStep ProofStep
  instance
    PLiftable PProofStep


newtype PProof (s :: S) = PProof (Term s (PBuiltinList PProofStep))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PProof where type DPTStrat _ = PlutusTypeNewtype

newtype PNeighbor (s :: S) = PNeighbor
  (Term s (PDataRecord '["nibble" ':= PInteger, "prefix" ':= PByteString, "root" ':= PByteString]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PDataFields, PIsData)

instance DerivePlutusType PNeighbor where type DPTStrat _ = PlutusTypeData

deriving via
  DeriveDataPLiftable PNeighbor Neighbor
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
  let go :: Term _ (PInteger :--> PBuiltinList PProofStep :--> PByteString)
      go = pfix #$ plam $ \self cursor steps ->
        pmatch steps $ \case
          PNil -> pnull_hash
          PCons x xs ->
            pmatch x $ \case
              PBranch fields ->
                pletFields @'["skip", "neighbors"] fields $ \branchF ->
                  plet (cursor + 1 + branchF.skip) $ \nextCursor ->
                  let root_ = (self # nextCursor # xs)
                  in pdo_branch # path # cursor # nextCursor # root_ # branchF.neighbors

              PFork fields ->
                pletFields @'["skip", "neighbor"] fields $ \forkF ->
                  pmatch xs $ \case
                    PNil ->
                      pletFields @'["prefix", "nibble", "root"] forkF.neighbor $ \neighborF ->
                        let prefix_ = pconsBS' # neighborF.nibble # neighborF.prefix
                        in pcombine # prefix_ # neighborF.root
                    PCons _ _ ->
                      plet (cursor + 1 + forkF.skip) $ \nextCursor ->
                        let root_ = (self # nextCursor # xs)
                        in pdo_fork # path # cursor # nextCursor # root_ # forkF.neighbor

              PLeaf fields ->
                pletFields @'["skip", "key", "value"] fields $ \leafF ->
                  pmatch xs $ \case
                    PNil ->
                      pcombine # (psuffix # leafF.key # cursor) # leafF.value
                    PCons _ _ ->
                      plet (cursor + 1 + leafF.skip) $ \nextCursor ->
                      plet leafF.key $ \leafKey ->
                      let root_ = (self # nextCursor # xs)
                          neighbor_ = ( pcon $ PNeighbor $
                            pdcons @"nibble" # pdata (pnibble # leafKey # cursor)
                              #$ pdcons @"prefix" # pdata (psuffix # leafKey # nextCursor)
                              #$ pdcons @"root" # leafF.value
                              #$ pdnil
                            )
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
  let go :: Term _ (PInteger :--> PBuiltinList PProofStep :--> PByteString)
      go = pfix #$ plam $ \self cursor steps ->
        pelimList (\proofStep ys ->
          pmatch proofStep $ \case
            PBranch fields ->
              ptraceInfo ("branch" <> pshow cursor) $
                pletFields @'["skip", "neighbors"] fields $ \branchF ->
                  plet (cursor + 1 + branchF.skip) $ \nextCursor ->
                    let root_ = self # nextCursor # ys
                    in pdo_branch # path # cursor # nextCursor # root_ # branchF.neighbors
            PFork fields ->
              pletFields @'["skip", "neighbor"] fields $ \forkF ->
                plet (cursor + 1 + forkF.skip) $ \nextCursor ->
                  let root_ = self # nextCursor # ys
                  in pdo_fork # path # cursor # nextCursor # root_ # forkF.neighbor
            PLeaf fields ->
              ptraceInfo ("leaf" <> pshow cursor) $
                pletFields @'["skip", "key", "value"] fields $ \leafF ->
                  plet (cursor + 1 + leafF.skip) $ \nextCursor ->
                    plet leafF.key $ \key_ ->
                      let neighbor_ = pcon $
                            PNeighbor $
                              pdcons @"nibble" # pdata (pnibble # key_ # (nextCursor - 1))
                                #$ pdcons @"prefix" # pdata (psuffix # key_ # nextCursor)
                                #$ pdcons @"root" # leafF.value
                                #$ pdnil
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
  pletFields @'["nibble", "prefix", "root"] neighbor_ $ \neighborF ->
  plet (pnibble # path # (nextCursor - 1)) $ \branch ->
  plet (pnibbles # path # cursor # (nextCursor - 1)) $ \prefix_ ->
  plet neighborF.nibble $ \neighborNibble ->
  pif (branch #== neighborNibble)
    perror
    (pcombine # prefix_ #
      (psparse_merkle_16 # branch # root_ #
        neighborNibble #
        (pcombine # neighborF.prefix # neighborF.root)))
