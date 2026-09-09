use super::super::VerifyError;
use super::check;
use super::fixtures::x3_certificate;

#[test]
fn normal_words_with_missing_word_rejected() {
    let mut tampered = x3_certificate();
    tampered.normal_words.remove(2);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::NormalWords {
            position: 2,
            expected: Some(vec![0, 0]),
            found: None,
        }
    );
}

#[test]
fn normal_words_with_extra_word_rejected() {
    let mut tampered = x3_certificate();
    tampered.normal_words.push(vec![0, 0, 0]);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::NormalWords {
            position: 3,
            expected: None,
            found: Some(vec![0, 0, 0]),
        }
    );
}

#[test]
fn normal_words_in_wrong_order_rejected() {
    let mut tampered = x3_certificate();
    tampered.normal_words.swap(1, 2);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::NormalWords {
            position: 1,
            expected: Some(vec![0]),
            found: Some(vec![0, 0]),
        }
    );
}
