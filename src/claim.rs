use nft_smt::common::{Byte32, Byte32Builder, BytesBuilder, CompactNFTInfo, OutPointBytesBuilder};
use nft_smt::smt::{blake2b_256, Blake2bHasher, H256, SMT};
use nft_smt::transfer::{ClaimedCommpactNFTValueVecBuilder, ClaimedCompactNFTKey, ClaimedCompactNFTKeyBuilder, ClaimedCompactNFTKeyVecBuilder, ClaimTransferCompactNFTEntriesBuilder, CompactNFTKey, CompactNFTKeyBuilder, CompactNFTKeyVecBuilder, OwnedCompactNFTValueVecBuilder, WithdrawCompactNFTValue, WithdrawTransferCompactNFTEntries};

use nft_smt::molecule::prelude::*;
use nft_smt::ckb_types::packed::{OutPointBuilder, OutPoint};

pub const BYTE3_ZEROS: [u8; 3] = [0u8; 3];
pub const BYTE22_ZEROS: [u8; 22] = [0u8; 22];

fn generate_claimed_compact_nft_smt(
    withdrawal_compact_nft_out_point: OutPoint,
    withdrawal_nft_keys: Vec<CompactNFTKey>,
    withdrawal_nft_values: Vec<WithdrawCompactNFTValue>,
    withdrawal_nft_proof: Vec<u8>,
    claim_leaves_count: usize,
) -> (H256, Vec<u8>) {
    let mut smt = SMT::default();

    let mut owned_nft_keys: Vec<CompactNFTKey> = Vec::new();
    let mut owned_nft_values: Vec<CompactNFTInfo> = Vec::new();
    let mut claimed_nft_keys: Vec<ClaimedCompactNFTKey> = Vec::new();
    let mut claimed_nft_values: Vec<Byte32> = Vec::new();
    let mut update_leaves: Vec<(H256, H256)> = Vec::with_capacity(claim_leaves_count * 2);
    for index in 0..claim_leaves_count {
        // Generate owned_nft smt kv pairs
        let withdrawal_nft_key = withdrawal_nft_keys.get(index).unwrap().clone();
        let mut nft_id_vec = Vec::new();
        nft_id_vec.extend(&BYTE3_ZEROS);
        nft_id_vec.extend(&[1u8]);
        nft_id_vec.extend(withdrawal_nft_key.nft_id().as_slice());
        let mut nft_id_bytes = [0u8; 32];
        nft_id_bytes.copy_from_slice(&nft_id_vec);
        let mut key = H256::from(nft_id_bytes);

        let owned_nft_key = CompactNFTKeyBuilder::default()
            .smt_type(Byte::from(1u8))
            .nft_id(withdrawal_nft_key.nft_id().clone())
            .build();
        owned_nft_keys.push(owned_nft_key);

        let withdrawal_nft_value = withdrawal_nft_values.get(index).unwrap().clone();
        let mut owned_nft_value_vec = Vec::new();
        owned_nft_value_vec.extend(&BYTE22_ZEROS);
        owned_nft_value_vec.extend(withdrawal_nft_value.nft_info().as_slice());
        let mut owned_nft_value_bytes = [0u8; 32];
        owned_nft_value_bytes.copy_from_slice(&owned_nft_value_vec);

        owned_nft_values.push(withdrawal_nft_value.nft_info().clone());
        let mut value: H256 = H256::from(owned_nft_value_bytes);

        update_leaves.push((key, value));
        smt.update(key, value).expect("SMT update leave error");

        // Generate claimed_nft smt kv pairs
        let compact_out_point_vec = withdrawal_compact_nft_out_point
            .as_bytes()
            .slice(12..36)
            .to_vec()
            .iter()
            .map(|v| Byte::from(*v))
            .collect::<Vec<Byte>>();
        let mut compact_out_point_bytes: [Byte; 24] = [Byte::from(0u8); 24];
        compact_out_point_bytes.copy_from_slice(&compact_out_point_vec);
        let compact_out_point = OutPointBytesBuilder::default()
            .set(compact_out_point_bytes)
            .build();
        let nft_key_ = CompactNFTKeyBuilder::default()
            .nft_id(withdrawal_nft_key.nft_id())
            .smt_type(Byte::from(3u8))
            .build();
        let claimed_nft_key = ClaimedCompactNFTKeyBuilder::default()
            .nft_key(nft_key_)
            .out_point(compact_out_point)
            .build();
        claimed_nft_keys.push(claimed_nft_key.clone());
        key = H256::from(blake2b_256(claimed_nft_key.as_slice()));

        value = H256::from([255u8; 32]);
        claimed_nft_values.push(
            Byte32Builder::default()
                .set([Byte::from(255u8); 32])
                .build(),
        );

        update_leaves.push((key, value));
        smt.update(key, value).expect("SMT update leave error");
    }
    let root_hash = smt.root().clone();

    let claim_mint_merkle_proof = smt
        .merkle_proof(update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let claim_mint_merkle_proof_compiled = claim_mint_merkle_proof
        .compile(update_leaves.clone())
        .unwrap();
    let verify_result = claim_mint_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, update_leaves.clone())
        .expect("smt proof verify failed");

    assert!(verify_result, "smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = claim_mint_merkle_proof_compiled.into();

    let merkel_proof_bytes = BytesBuilder::default()
        .extend(merkel_proof_vec.iter().map(|v| Byte::from(*v)))
        .build();

    let withdraw_merkel_proof_bytes = BytesBuilder::default()
        .extend(withdrawal_nft_proof.iter().map(|v| Byte::from(*v)))
        .build();

    let claim_entries = ClaimTransferCompactNFTEntriesBuilder::default()
        .owned_nft_keys(
            CompactNFTKeyVecBuilder::default()
                .set(owned_nft_keys)
                .build(),
        )
        .owned_nft_values(
            OwnedCompactNFTValueVecBuilder::default()
                .set(owned_nft_values)
                .build(),
        )
        .claimed_nft_keys(
            ClaimedCompactNFTKeyVecBuilder::default()
                .set(claimed_nft_keys)
                .build(),
        )
        .claimed_nft_values(
            ClaimedCommpactNFTValueVecBuilder::default()
                .set(claimed_nft_values)
                .build(),
        )
        .proof(merkel_proof_bytes)
        .withdrawal_proof(withdraw_merkel_proof_bytes)
        .build();

    (
        root_hash,
        Vec::from(claim_entries.as_slice()),
    )
}

#[test]
fn test_claim() {
    let mut withdrawal_tx_hash_bytes: [u8; 32] = [0u8; 32];
    withdrawal_tx_hash_bytes.copy_from_slice(&hex::decode("bfa0d4d9e7b3a64bae320eafa32cd26079d351ae8953d511bd322544fc2ba94a").unwrap());
    // Uint32 little endian
    let index = [0u8, 0u8, 0u8, 0u8].map(|v| nft_smt::ckb_types::packed::Byte::from(v));
    let withdrawal_compact_nft_out_point = OutPointBuilder::default()
        .tx_hash(nft_smt::ckb_types::packed::Byte32::new(withdrawal_tx_hash_bytes))
        .index(nft_smt::ckb_types::packed::Uint32Builder::default().set(index).build())
        .build();
    println!("input_compact_nft_out_point: {:?}", withdrawal_compact_nft_out_point);

    let withdrawal_entries_bytes = hex::decode("f100000018000000390000004700000068000000a200000001000000013939ecec56db8161b6308c84d6f5f9f12d00d1f00000000300000002010000000505050505050505000001000000023939ecec56db8161b6308c84d6f5f9f12d00d1f00000000300000002010000000505050505050505000066abc04e590ca014a7433cb21f2a079a7ba18335a32cd26079d351ae8953d511bd322544fc2ba94a000000004b0000004c4f194c4f19484fe551ff0c8f4a64e8ecad6b62806799a0ff51b449a69afb6bed0a10c93d746da54a4fb4cb8d04b805790429388958cf4c3f60caddae39b57014805172e97236c92a2762").unwrap();
    let withdrawal_entries = WithdrawTransferCompactNFTEntries::from_slice(&withdrawal_entries_bytes).unwrap();

    let mut withdrawal_nft_keys = Vec::new();
    for nft_key in withdrawal_entries.withdrawal_nft_keys().into_iter() {
        withdrawal_nft_keys.push(nft_key);
    }
    let mut withdrawal_nft_values = Vec::new();
    for nft_value in withdrawal_entries.withdrawal_nft_values().into_iter() {
        withdrawal_nft_values.push(nft_value);
    }

    let withdrawal_nft_proof = withdrawal_entries.proof().raw_data().to_vec();

    println!("withdrawal_nft_keys: {:?}", withdrawal_nft_keys.clone());
    println!("withdrawal_nft_values: {:?}", withdrawal_nft_values.clone());
    println!("withdrawal_nft_proof: {:?}", withdrawal_nft_proof);

    let (root_hash, witness_data) = generate_claimed_compact_nft_smt(withdrawal_compact_nft_out_point, withdrawal_nft_keys, withdrawal_nft_values, withdrawal_nft_proof, 1);

    println!("root_hash: {:?}", hex::encode(root_hash.as_slice()));
    println!("witness_data: {:?}", hex::encode(witness_data));
}