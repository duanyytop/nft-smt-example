use nft_smt::common::{BytesBuilder, CharacteristicBuilder, CompactNFTIdBuilder, CompactNFTInfo, CompactNFTInfoBuilder, IssuerIdBuilder, LockHashBuilder, OutPointBytesBuilder, Uint32Builder};
use nft_smt::smt::{blake2b_256, Blake2bHasher, H256, SMT};
use nft_smt::transfer::{ClaimedCompactNFTKeyBuilder, CompactNFTKey, CompactNFTKeyBuilder, CompactNFTKeyVecBuilder, OwnedCompactNFTValueVecBuilder, WithdrawCompactNFTValue, WithdrawCompactNFTValueBuilder, WithdrawCompactNFTValueVecBuilder, WithdrawTransferCompactNFTEntriesBuilder};

use nft_smt::molecule::prelude::*;
use nft_smt::ckb_types::packed::{OutPointBuilder, OutPoint};

const BYTE3_ZEROS: [u8; 3] = [0u8; 3];
const BYTE22_ZEROS: [u8; 22] = [0u8; 22];

fn generate_withdrawal_smt(
    input_compact_nft_out_point: OutPoint,
    to: [Byte; 20],
    class_type_args: Vec<u8>,
    withdrawal_leaves_count: usize,
) -> (H256, Vec<u8>) {
    let class_type_args_bytes = class_type_args
        .iter()
        .map(|v| Byte::from(*v))
        .collect::<Vec<Byte>>();

    let mut smt = SMT::default();

    let mut owned_nft_keys: Vec<CompactNFTKey> = Vec::new();
    let mut owned_nft_values: Vec<CompactNFTInfo> = Vec::new();
    let mut withdrawal_nft_keys: Vec<CompactNFTKey> = Vec::new();
    let mut withdrawal_nft_values: Vec<WithdrawCompactNFTValue> = Vec::new();
    let mut update_leaves: Vec<(H256, H256)> = Vec::with_capacity(withdrawal_leaves_count * 2);

    let mut token_id_bytes = [Byte::from(0u8); 4];

    for index in 0..withdrawal_leaves_count {
        let mut issuer_id_bytes = [Byte::from(0); 20];
        issuer_id_bytes.copy_from_slice(&class_type_args_bytes[0..20]);
        let issuer_id = IssuerIdBuilder::default().set(issuer_id_bytes).build();

        let mut class_id_bytes = [Byte::from(0); 4];
        class_id_bytes.copy_from_slice(&class_type_args_bytes[20..24]);
        let class_id = Uint32Builder::default().set(class_id_bytes).build();

        token_id_bytes[3] = Byte::from((index + 2) as u8);
        let token_id = Uint32Builder::default().set(token_id_bytes).build();
        let nft_id = CompactNFTIdBuilder::default()
            .issuer_id(issuer_id)
            .class_id(class_id)
            .token_id(token_id)
            .build();
        let owned_nft_key = CompactNFTKeyBuilder::default()
            .nft_id(nft_id.clone())
            .smt_type(Byte::from(1u8))
            .build();
        let mut nft_id_vec = Vec::new();
        nft_id_vec.extend(&BYTE3_ZEROS);
        nft_id_vec.extend(&[1u8]);
        nft_id_vec.extend(nft_id.as_slice());
        let mut nft_id_bytes = [0u8; 32];
        nft_id_bytes.copy_from_slice(&nft_id_vec);

        let mut key = H256::from(nft_id_bytes);
        owned_nft_keys.push(owned_nft_key);

        let characteristic = CharacteristicBuilder::default()
            .set([Byte::from(5); 8])
            .build();
        let owned_nft_value = CompactNFTInfoBuilder::default()
            .characteristic(characteristic)
            .configure(Byte::from(0u8))
            .state(Byte::from(0u8))
            .build();
        let mut nft_info_vec = Vec::new();
        nft_info_vec.extend(&BYTE22_ZEROS);
        nft_info_vec.extend(owned_nft_value.as_slice());
        let mut nft_info_bytes = [0u8; 32];
        nft_info_bytes.copy_from_slice(&nft_info_vec);
        owned_nft_values.push(owned_nft_value.clone());

        let value = H256::from(nft_info_bytes);



        // Add old owned smt leaves
        smt.update(key, value).expect("SMT update leave error");




        smt.update(key, H256::from([0u8; 32])).expect("SMT update leave error");
        update_leaves.push((key, H256::from([0u8; 32])));

        let withdrawal_nft_key = CompactNFTKeyBuilder::default()
            .smt_type(Byte::from(2u8))
            .nft_id(nft_id.clone())
            .build();




        // Add old claimed smt leaves
        let claimed_out_point = hex::decode("b30aec8032f7ad2aa55cf198238bd41c4a735c4767640fa50b45fc9a951f892b01000000").unwrap();
        let compact_out_point_vec = claimed_out_point[12..36]
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
            .nft_id(nft_id.clone())
            .smt_type(Byte::from(2u8))
            .build();
        let claimed_nft_key = ClaimedCompactNFTKeyBuilder::default()
            .nft_key(nft_key_)
            .out_point(compact_out_point)
            .build();
        key = H256::from(blake2b_256(claimed_nft_key.as_slice()));
        nft_id_bytes[3] = 2u8;
        smt.update(key, H256::from([255u8; 32])).expect("SMT update leave error");





        nft_id_bytes[3] = 2u8;
        key = H256::from(nft_id_bytes);
        withdrawal_nft_keys.push(withdrawal_nft_key);

        let compact_out_point_vec = input_compact_nft_out_point
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
        let nft_info = owned_nft_value.clone();
        let withdrawal_nft_value = WithdrawCompactNFTValueBuilder::default()
            .nft_info(nft_info)
            .out_point(compact_out_point)
            .to(LockHashBuilder::default().set(to).build())
            .build();
        withdrawal_nft_values.push(withdrawal_nft_value.clone());
        let value = H256::from(blake2b_256(withdrawal_nft_value.as_slice()));

        smt.update(key, value).expect("SMT update leave error");
        update_leaves.push((key, value));
    }

    println!("owned_nft_keys: {:?}", owned_nft_keys);

    let root_hash = smt.root().clone();

    let withdrawal_merkle_proof = smt
        .merkle_proof(update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let withdrawal_merkle_proof_compiled = withdrawal_merkle_proof
        .compile(update_leaves.clone())
        .unwrap();

    let verify_result = withdrawal_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, update_leaves.clone())
        .expect("smt proof verify failed");
    assert!(verify_result, "after withdrawal smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = withdrawal_merkle_proof_compiled.into();
    let merkel_proof_bytes = BytesBuilder::default()
        .extend(merkel_proof_vec.iter().map(|v| Byte::from(*v)))
        .build();

    let withdrawal_entries = WithdrawTransferCompactNFTEntriesBuilder::default()
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
        .withdrawal_nft_keys(
            CompactNFTKeyVecBuilder::default()
                .set(withdrawal_nft_keys)
                .build(),
        )
        .withdrawal_nft_values(
            WithdrawCompactNFTValueVecBuilder::default()
                .set(withdrawal_nft_values)
                .build(),
        )
        .proof(merkel_proof_bytes)
        .build();

    (
        root_hash,
        Vec::from(withdrawal_entries.as_slice()),
    )
}

#[test]
fn test_withdraw() {
    let class_args = hex::decode("3939ecec56db8161b6308c84d6f5f9f12d00d1f000000003").unwrap();

    let mut tx_hash_bytes: [u8; 32] = [0u8; 32];
    tx_hash_bytes.copy_from_slice(&hex::decode("bfa0d4d9e7b3a64bae320eafa32cd26079d351ae8953d511bd322544fc2ba94a").unwrap());
    // Uint32 little endian
    let index = [0u8, 0u8, 0u8, 0u8].map(|v| nft_smt::ckb_types::packed::Byte::from(v));
    let input_compact_nft_out_point = OutPointBuilder::default()
        .tx_hash(nft_smt::ckb_types::packed::Byte32::new(tx_hash_bytes))
        .index(nft_smt::ckb_types::packed::Uint32Builder::default().set(index).build())
        .build();

    let to_lock_hash = vec![102, 171, 192,  78,  89,  12, 160,  20, 167,  67,  60, 178,  31,  42,   7, 154,
        123, 161, 131,  53];
    let mut to: [Byte; 20] = [Byte::from(0); 20];
    to.copy_from_slice(&to_lock_hash.iter().map(|v| Byte::from(*v)).collect::<Vec<Byte>>());

    let (root_hash, witness_data) = generate_withdrawal_smt(input_compact_nft_out_point, to, class_args, 1);

    println!("root_hash: {:?}", hex::encode(root_hash.as_slice()));
    println!("witness_data: {:?}", hex::encode(witness_data));
}