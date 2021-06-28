use std::convert::{TryFrom};
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use std::io::{Error, ErrorKind};

macro_rules! unwrap_or_return {
    ( $e:expr ) => {
        match $e {
            Ok(x) => x,
            Err(e) => return Err(e),
        }
    }
}

macro_rules! make_function_fixed_array
{
($n: ident, $l: literal) => {
    fn $n(data: &[u8]) -> [u8; $l]
    {
        let mut output: [u8; $l] = [0; $l];
        for i in 0usize..$l
        {
            output[i] = data[i];
        }
        output
    }
};
}

make_function_fixed_array!(mk_fixed_array2, 2);
make_function_fixed_array!(mk_fixed_array4, 4);


pub struct BejDictEntry {
    pub(crate) format: BejFormat,
    pub(crate) name: String,
    pub(crate) seqnum: u16,
    pub(crate) children: Vec<u16>,
    pub(crate) nullable: bool,
    pub(crate) readonly: bool,
    pub(crate) dbinding: bool
}

impl Clone for BejDictEntry {
    fn clone(&self) -> Self {
        let mut other: Self = BejDictEntry {
            format: BejFormat::Set,
            name: "".to_string(),
            seqnum: 0,
            children: vec![],
            nullable: false,
            readonly: false,
            dbinding: false
        };
        other.children = self.children.clone();
        other.format = self.format;
        other.name = self.name.clone();
        other.seqnum = self.seqnum;
        other.nullable = self.nullable;
        other.readonly = self.readonly;
        other.dbinding = self.dbinding;
        other
    }
}

pub struct BejDict {
    pub(crate) version_tag: u8,
    pub(crate) truncation: bool,
    pub(crate) version: BejVersion,
    pub(crate) entries: Vec<BejDictEntry>
}

pub struct BejHeader {
    pub(crate) version_tag: u8,
    pub(crate) truncation: bool,
    pub(crate) entry_count: u16,
    pub(crate) version: BejVersion,
    pub(crate) dict_size: u32
}

pub struct BejVersion {
    pub(crate) major: Option<u8>,
    pub(crate) medium: Option<u8>,
    pub(crate) minor: Option<u8>,
    pub(crate) tiny: Option<u8>
}

#[derive(FromPrimitive)]
enum BejSchemaClass {
    Major = 0,
    Event = 1,
    Annotation = 2,
    CollectionMemberType = 3,
    Error = 4,
    Registry = 5
}

pub struct BejEncoding {
    version: BejVersion,
    class: BejSchemaClass,
    tuple: BejTuple
}

enum BejValue {
    Null,
    Integer(i64),
    Enum(u64),
    String(String),
    Real(f64),
    Boolean(bool),
    Bytestring(std::io::Bytes<u8>),
    Set(Vec<BejTuple>),
    Array(Vec<BejTuple>),
    Choice(Box<BejTuple>),
    PropertyAnnotation(Box<BejTuple>),
    RegistryItem(u64),
    ResourceLink(u64),
    ResourceLinkExpansion(u64, Vec<u8>),
}

pub type BejLocator = Vec<u64>;

impl std::fmt::Display for BejValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BejValue::Null => write!(f, "NULL"),
            BejValue::String(s) => write!(f, "{}", s),
            BejValue::Set(d) => {
                write!(f, "{{")?;
                for el in d {
                    write!(f, "{},", el)?;
                }
                write!(f, "}}")
            },
            _ => Err(Default::default())
        }
    }
}

#[derive(Debug, Copy, Clone, FromPrimitive)]
pub enum BejFormat {
    Set = 0,
    Array = 1,
    Null = 2,
    Integer = 3,
    Enum = 4,
    String = 5,
    Real = 6,
    Boolean = 7,
    Bytestring = 8,
    Choice = 9,
    PropertyAnnotations = 10,
    RegistryItem = 11,
    ResourceLink = 14,
    ResourceLinkExpansion = 15,
}

impl TryFrom<u8> for BejFormat {
    type Error = std::io::Error;

    fn try_from(v: u8) -> Result<BejFormat, Error> {
        match v >> 4 {
            0 => Ok(BejFormat::Set),
            1 => Ok(BejFormat::Array),
            2 => Ok(BejFormat::Null),
            3 => Ok(BejFormat::Integer),
            4 => Ok(BejFormat::Enum),
            5 => Ok(BejFormat::String),
            6 => Ok(BejFormat::Real),
            7 => Ok(BejFormat::Boolean),
            8 => Ok(BejFormat::Bytestring),
            9 => Ok(BejFormat::Choice),
            10 => Ok(BejFormat::PropertyAnnotations),
            11 => Ok(BejFormat::RegistryItem),
            14 => Ok(BejFormat::ResourceLink),
            15 => Ok(BejFormat::ResourceLinkExpansion),
            _ => Err(Error::new(std::io::ErrorKind::InvalidData, format!("Failed to parse BEJ format: 0x{:x}", v))),
        }
    }
}

impl PartialEq for BejFormat {
    fn eq(&self, other: &Self) -> bool {
        self == other
    }
}

pub struct BejTuple {
    seqnum: u64,
    value: BejValue
}

pub trait BejDecoder {
    fn decode(&self, dict: &BejDict, locator: BejLocator) -> Result<String, Error>;
}

impl BejDecoder for BejTuple {
    fn decode(&self, dict: &BejDict, locator: BejLocator) -> Result<String, Error> {
        let mut output: String = String::new();
        let cached_loc: BejLocator = locator.clone();
        let is_root = locator.len() == 0;
        let mut value: String;
        if is_root {
            output.push('{');
        }

        let dentry = match get_dict_entry_by_locator(dict, locator) {
            Ok(l) => l,
            Err(e) => return Err(e)
        };
        output.push_str(format!("\"{}\": ", dentry.name).as_str());
        output.push_str(match &self.value {
            BejValue::Set(ref v) => {
                value = String::new();
                value.push('{');
                for ob in v {
                    if ob.seqnum != v[0].seqnum {
                        value.push(',');
                        value.push(' ');
                    }
                    let mut lctr = cached_loc.to_owned();
                    lctr.push(ob.seqnum);
                    let serialized = match ob.decode(dict, lctr) {
                        Ok(v) => v,
                        Err(e) => return Err(e)
                    };
                    value.push_str(serialized.as_str())
                }
                value.push('}');
                value.as_str()
            },
            BejValue::Array(v) => {
                value = String::new();
                value.push('[');
                for ob in v {
                    if ob.seqnum != v[0].seqnum {
                        value.push(',');
                        value.push(' ');
                    }
                    let mut lctr = cached_loc.to_owned();
                    lctr.push(ob.seqnum);
                    let serialized = match ob.decode(dict, lctr) {
                        Ok(v) => v,
                        Err(e) => return Err(e)
                    };
                    value.push_str(serialized.as_str())
                }
                value.push(']');
                value.as_str()
            },
            BejValue::String(v) => {
                value = String::new();
                value.push('\"');
                value.push_str(v);
                value.push('\"');
                value.as_str()
            },
            _ => "unsupported type"
        });
        if is_root {
            output.push('}');
        }
        Ok(output)
    }
}

impl std::fmt::Display for BejTuple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{ {}: {} }}", self.seqnum, self.value)
    }
}

fn read_nnint(arr: &[u8]) -> Result<(usize, u64), Error>
{
    if arr.len() == 0 {
        Err(Error::new(std::io::ErrorKind::InvalidData, "Zero length"))
    } else {
        let nbytes = usize::from(arr[0]);
        if arr.len() < nbytes + 1 {
            Err(Error::new(std::io::ErrorKind::InvalidData, format!("Inconsistant length {} vs. {}", arr.len(), nbytes + 1)))
        } else {
            let mut multiplier: u64 = 1;
            let mut v: u64 = 0;
            for idx in 1..nbytes + 1 {
                v += (arr[idx] as u64) * multiplier;
                multiplier *= 256;
            }
            Ok((nbytes + 1, v))
        }
    }
}

pub fn parse_bej_version(data: &[u8]) -> Result<BejVersion, Error> {
    if data.len() != 4 {
        Err(Error::new(ErrorKind::InvalidData,
                       format!("Expected version length not equal 4, it is {}", data.len())))
    } else {
        let major = if (data[3] & 0xF0) == 0xF0 { Some(data[3] & 0x0F) } else {
            return Ok(BejVersion { major: None, medium: None, minor: None, tiny: None })
        };
        let medium = if (data[2] & 0xF0) == 0xF0 { Some(data[2] & 0x0F) } else {
            return Ok(BejVersion { major, medium: None, minor: None, tiny: None })
        };
        let minor = if (data[1] & 0xF0) == 0xF0 { Some(data[1] & 0x0F) } else {
            return Ok(BejVersion { major, medium, minor: None, tiny: None })
        };
        if (data[0] & 0xF0) == 0xF0 {
            Ok(BejVersion { major, medium, minor, tiny: Some(data[0] & 0x0F) })
        } else {
            Ok(BejVersion { major, medium, minor, tiny: None })
        }
    }
}

fn parse_bej_string(bts: &[u8]) -> Result<BejValue, Error>
{
    match String::from_utf8(bts[0..bts.len()-1].to_vec()) {
        Ok(r) => Ok(BejValue::String(r)),
        Err(_) => Err(Error::new(std::io::ErrorKind::InvalidData, "Failed to parse string"))
    }
}

fn parse_bej_set(data: &[u8]) -> Result<BejValue, Error>
{
    let (s, v) = read_nnint(data).unwrap();
    let mut offset: usize = s;
    let mut tuples: Vec<BejTuple> = Vec::new();
    for _ in 0..v {
        let (tpl, len) = unwrap_or_return!(create_bej_tuple(&data[offset..]));
        offset += len;
        tuples.push(tpl);
    }
    Ok(BejValue::Set(tuples))
}

fn parse_bej_value(format: BejFormat, data: &[u8]) -> Result<BejValue, Error>
{
    match format {
        BejFormat::Set => parse_bej_set(data),
        BejFormat::Array => Err(Error::new(std::io::ErrorKind::InvalidData, "Arrays are not yet supported")),
        BejFormat::Null => Err(Error::new(std::io::ErrorKind::InvalidData, "Nulls are not yet supported")),
        BejFormat::Integer => Err(Error::new(std::io::ErrorKind::InvalidData, "Integers are not yet supported")),
        BejFormat::Enum => Err(Error::new(std::io::ErrorKind::InvalidData, "Enums are not yet supported")),
        BejFormat::String => parse_bej_string(data),
        BejFormat::Real => Err(Error::new(std::io::ErrorKind::InvalidData, "Reals are not yet supported")),
        BejFormat::Boolean => Err(Error::new(std::io::ErrorKind::InvalidData, "Bools are not yet supported")),
        BejFormat::Bytestring => Err(Error::new(std::io::ErrorKind::InvalidData, "Bytestrings are not yet supported")),
        BejFormat::Choice => Err(Error::new(std::io::ErrorKind::InvalidData, "Choices are not yet supported")),
        BejFormat::PropertyAnnotations => Err(Error::new(std::io::ErrorKind::InvalidData, "Property annotations are not yet supported")),
        BejFormat::RegistryItem => Err(Error::new(std::io::ErrorKind::InvalidData, "Registry items are not yet supported")),
        BejFormat::ResourceLink => Err(Error::new(std::io::ErrorKind::InvalidData, "Resource Links are not yet supported")),
        BejFormat::ResourceLinkExpansion => Err(Error::new(std::io::ErrorKind::InvalidData, "Resource link expansions are not yet supported")),
    }
}

pub fn create_bej_tuple(binary: &[u8]) -> Result<(BejTuple, usize), Error>
{
    let (len, seqnum) = unwrap_or_return!(read_nnint(binary));
    let format = unwrap_or_return!(BejFormat::try_from(binary[len]));
    let (len2, tuple_length) = unwrap_or_return!(read_nnint(&binary[(len+1)..]));
    if tuple_length > 0 {
        let offset = len + len2 + 1;
        let value = unwrap_or_return!(parse_bej_value(format, &binary[offset..offset + tuple_length as usize]));
        Ok((BejTuple { seqnum, value}, tuple_length as usize + len + len2 + 1))
    } else {
        Ok((BejTuple { seqnum, value: BejValue::Null}, tuple_length as usize + len + len2 + 1))
    }
}

pub fn create_bej_encoding(data: &[u8]) -> Result<BejEncoding, Error>
{
    let sch_class: BejSchemaClass = match FromPrimitive::from_u8(data[6]) {
        Some(v) => v,
        None => return Err(Error::new(std::io::ErrorKind::InvalidData, "Failed to parse string"))
    };

    let version = match parse_bej_version(&data[0..4]) {
        Ok(v) => v,
        Err(e) => return Err(e)
    };

    let (tuple, _) = match create_bej_tuple(&data[7..]) {
        Ok(v) => v,
        Err(e) => return Err(e)
    };

    return Ok(BejEncoding {version, class: sch_class, tuple})
}

fn get_locators(prefix: BejLocator, t: &BejTuple) -> Vec<BejLocator> {
    let mut val: Vec<BejLocator> = Vec::new();
    let mut new_loc = prefix.clone();
    new_loc.push(t.seqnum);
    val.push(new_loc);
    match t.value {
        BejValue::Set(ref v) | BejValue::Array(ref v) => {
            let mut new_loc = prefix.clone();
            new_loc.push(t.seqnum);
            for loc in v.iter().map(|elem| get_locators(new_loc.clone(), elem)) {
                val.extend(loc);
            }
        },
        _ => {}
    };
    val
}

fn get_bej_next_locator(enc: &BejEncoding, locator: BejLocator) -> Result<BejLocator, Error> {
    get_bej_tuple_next_locator(&enc.tuple, locator)
}

fn get_bej_tuple_next_locator(tuple: &BejTuple, locator: BejLocator) -> Result<BejLocator, Error> {
    let locators = get_locators(vec![], &tuple);
    if locator.len() == 0 {
        return Ok(locators[0].clone());
    }

    for i in 0..locators.len() - 1 {
        if locators[i] == locator {
            return Ok(locators[i + 1].clone());
        }
    }
    Err(Error::new(std::io::ErrorKind::InvalidData, "Not found locator"))
}

fn get_bej_value_by_locator(enc: &BejEncoding, locator: BejLocator)-> Result<&BejValue, Error> {
    let mut tuple = &enc.tuple;
    if tuple.seqnum != locator[0] {
        return Err(Error::new(std::io::ErrorKind::InvalidData, "Bad BEJ locator"))
    }

    for it in 1..locator.len() {
        tuple = match tuple.value {
            BejValue::Set(ref v) | BejValue::Array(ref v) => {
                let fnd = v.iter().find(|val| val.seqnum == locator[it]);
                match fnd {
                    Some(a) => a,
                    None => return Err(Error::new(std::io::ErrorKind::InvalidData, "Bad BEJ locator"))
                }
            }
            _ => {
                return Err(Error::new(std::io::ErrorKind::InvalidData, "Bad BEJ locator"))
            }
        }
    }
    Ok(&tuple.value)
}

pub fn get_dict_entry_by_locator(dict: &BejDict, locator: BejLocator) -> Result<BejDictEntry, Error> {
    let mut entry_offset = 0;
    for ii in 0..locator.len() {
        if ii == locator.len() - 1 {
            return Ok(dict.entries[entry_offset].clone());
        }
        match dict.entries[entry_offset].format {
            BejFormat::Set | BejFormat::Array => {
                for child in dict.entries[entry_offset].children.clone() {
                    let dic_off = child as usize;
                    if locator[ii + 1] == 2 * dict.entries[dic_off].seqnum as u64 {
                        entry_offset = dic_off;
                    }
                }
            },
            _ => {}
        }
    }
    Err(Error::new(ErrorKind::InvalidData, "Failed to find locator item. Reached end of function"))
}

fn parse_bej_header(data: &[u8]) -> Result<BejHeader, Error> {
    if data.len() < 12 {
        Err(Error::new(ErrorKind::InvalidData,
                       format!("Expected header length more than 12, not {}", data.len())))
    } else {
        let version_tag = data[0];
        let truncation = (data[1] & 0x1) > 0;
        let entry_count = u16::from_le_bytes(mk_fixed_array2(&data[2..4]));
        let version = match parse_bej_version(&data[4..8]) {
            Ok(v) => v,
            Err(e) => return Err(e)
        };
        let dictionary_size = u32::from_le_bytes(mk_fixed_array4(&data[8..12]));
        Ok({
            BejHeader {
                version_tag, truncation, entry_count, version,
                dict_size: dictionary_size
            }
        })
    }
}

fn parse_bej_dict_entry(entry: u16, data: &[u8]) -> Result<BejDictEntry, Error> {
    let raw_entry = &data[(12 + 10 * entry) as usize..(12 + 10 * (entry + 1)) as usize];
    let name_offset = u16::from_le_bytes(mk_fixed_array2(&raw_entry[8..10]));
    let name_length = raw_entry[7] as u16;
    let name = if name_length == 0 {
        String::from("")
    } else {
        match String::from_utf8(Vec::from(&data[name_offset as usize..(name_offset + name_length - 1) as usize])) {
            Ok(v) => v,
            Err(_) => return Err(Error::new(std::io::ErrorKind::InvalidData, "Failed to parse name string"))
        }
    };
    let seqnum = u16::from_le_bytes(mk_fixed_array2(&raw_entry[1..3]));
    let child_count = u16::from_le_bytes(mk_fixed_array2(&raw_entry[5..7]));
    let children = if child_count > 0 {
        let child_entry = (u16::from_le_bytes(mk_fixed_array2(&raw_entry[3..5])) - 12) / 10;
        (child_entry..(child_entry + child_count)).collect()
    } else {
        Vec::new()
    };

    let format_raw = raw_entry[0];
    let fmt = match BejFormat::try_from(format_raw) {
        Ok(v) => v,
        Err(_) => return Err(Error::new(ErrorKind::InvalidData, "Failed to convert format"))
    };
    let dbinding = (format_raw & 0x01) > 0;
    let readonly = (format_raw & 0x02) > 0;
    let nullable = (format_raw & 0x04) > 0;
    Ok(BejDictEntry {
        format: fmt,
        name, seqnum, children, nullable, readonly, dbinding
    })
}

pub fn parse_bej_dict(data: &[u8]) -> Result<BejDict, Error> {
    let hdr = match parse_bej_header(&data[0..12]) {
        Ok(hdr) => hdr,
        Err(e) => return Err(e)
    };
    let mut entries: Vec<BejDictEntry> = Vec::new();

    for i in 0..hdr.entry_count {
        entries.push(match parse_bej_dict_entry(i, data) {
            Ok(v) => v,
            Err(e) => return Err(e)
        });
    }
    Ok(BejDict { version_tag: hdr.version_tag, truncation: hdr.truncation, version: hdr.version, entries })
}

#[test]
fn test_get_entry_by_locator() {
    let example_dict: [u8;141] = [
        0x00, 0x00, 0x06, 0x00, 0xff, 0xff, 0xff, 0xff, 0x8d, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x16, 0x00, 0x04, 0x00, 0x0e, 0x48, 0x00,//0
        0x56, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0c, 0x56, 0x00,//1
        0x16, 0x01, 0x00, 0x3e, 0x00, 0x01, 0x00, 0x08, 0x62, 0x00,//2
        0x52, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05, 0x6a, 0x00,//3
        0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x6f, 0x00,//4
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,//5
        0x4a, 0x6f, 0x62, 0x43, 0x6f, 0x6c, 0x6c, 0x65,//Copyright
        0x63, 0x74, 0x69, 0x6f, 0x6e, 0x00, 0x44, 0x65, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x69, 0x6f,
        0x6e, 0x00, 0x4d, 0x65, 0x6d, 0x62, 0x65, 0x72, 0x73, 0x00, 0x4e, 0x61, 0x6d, 0x65, 0x00, 0x4f,
        0x65, 0x6d, 0x00, 0x19, 0x43, 0x6f, 0x70, 0x79, 0x72, 0x69, 0x67, 0x68, 0x74, 0x20, 0x32, 0x30,
        0x31, 0x34, 0x2d, 0x32, 0x30, 0x32, 0x30, 0x20, 0x44, 0x4d, 0x54, 0x46, 0x00];
    let dict = parse_bej_dict(&example_dict).unwrap();

    let dentry0 = get_dict_entry_by_locator(&dict, vec![0]).unwrap();
    let dentry1 = get_dict_entry_by_locator(&dict, vec![0, 0]).unwrap();
    let dentry2 = get_dict_entry_by_locator(&dict, vec![0, 2]).unwrap();
    let dentry3 = get_dict_entry_by_locator(&dict, vec![0, 4]).unwrap();
    let dentry4 = get_dict_entry_by_locator(&dict, vec![0, 6]).unwrap();
    assert_eq!(dentry0.seqnum, 0);
    assert_eq!(dentry0.name, String::from("JobCollection"));
    assert!(matches!(dentry0.format, BejFormat::Set));
    assert_eq!(dentry1.seqnum, 0);
    assert_eq!(dentry1.name, String::from("Description"));
    assert!(matches!(dentry1.format, BejFormat::String));
    assert_eq!(dentry2.seqnum, 1);
    assert_eq!(dentry2.name, String::from("Members"));
    assert!(matches!(dentry2.format, BejFormat::Array));
    assert_eq!(dentry3.seqnum, 2);
    assert_eq!(dentry3.name, String::from("Name"));
    assert!(matches!(dentry3.format, BejFormat::String));
    assert_eq!(dentry4.seqnum, 3);
    assert_eq!(dentry4.name, String::from("Oem"));
    assert!(matches!(dentry4.format, BejFormat::Set));
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_decode_nint_ok() {
        let data:[u8;4] = [3,1,0,0];
        let (len, v) = read_nnint(&data).unwrap();
        assert_eq!(v, 1);
        assert_eq!(len, 4);
    }

    #[test]
    fn test_try_bejformat() {
        assert_eq!(true, BejFormat::try_from(0).is_ok());
        assert_eq!(true, BejFormat::try_from(1).is_ok());
        assert_eq!(true, BejFormat::try_from(3).is_ok());
        assert_eq!(true, BejFormat::try_from(6).is_ok());
        assert_eq!(true, BejFormat::try_from(0xC0).is_err());
    }

    #[test]
    fn test_decode_nil_tuple() {
        let data:[u8;4] = [3,1,0,0];
        let (len, v) = read_nnint(&data).unwrap();
        assert_eq!(v, 1);
        assert_eq!(len, 4);
    }

    #[test]
    fn test_decode_bej_tuple_string() {
        let data:[u8; 11] = [1,1,0x50,1,6,'t' as u8,'a' as u8,'r' as u8,'a' as u8,'s' as u8,'\0' as u8];
        let r = create_bej_tuple(&data).unwrap();
        assert_eq!(r.1, 11);
    }

    #[test]
    fn test_tuple_binary() {
        let data:[u8;27] = [0x01u8, 0x00u8, 0x00u8, 0x01u8, 0x16u8, 0x01u8, 0x01u8, 0x01u8, 0x32u8,
                            0x00u8, 0x01u8, 0x0Fu8, 0x01u8, 0x01u8, 0x01u8, 0x00u8, 0x50u8, 0x01u8,
                            0x08u8, 0x7Au8, 0x61u8, 0x6Cu8, 0x6Fu8, 0x6Fu8, 0x70u8, 0x61u8, 0x00u8];
        let r = create_bej_tuple(&data).unwrap();
        assert_eq!(r.1, 27)
    }

    #[test]
    fn test_bej_encoding() {
        let data: [u8; 34] = [  0x00, 0xf0, 0xf0, 0xf1, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x01,
                                0x16, 0x01, 0x01, 0x01, 0x32, 0x00, 0x01, 0x0f, 0x01, 0x01, 0x01,
                                0x00, 0x50, 0x01, 0x08, 0x7a, 0x61, 0x6c, 0x6f, 0x6f, 0x70, 0x61,
                                0x00];
        let encoding_raw = create_bej_encoding(&data);
        assert_eq!(encoding_raw.is_ok(), true);
        let encoding = encoding_raw.unwrap();
        assert_eq!(encoding.version.major, Some(1));
        assert_eq!(encoding.version.medium, Some(0));
        assert_eq!(encoding.version.minor, Some(0));
        assert_eq!(encoding.version.tiny, None);
        assert!(matches!(encoding.class, BejSchemaClass::Major));
    }

    #[test]
    fn test_get_locators_list() {
        let data: [u8; 34] = [  0x00, 0xf0, 0xf0, 0xf1, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x01,
            0x16, 0x01, 0x01, 0x01, 0x32, 0x00, 0x01, 0x0f, 0x01, 0x01, 0x01,
            0x00, 0x50, 0x01, 0x08, 0x7a, 0x61, 0x6c, 0x6f, 0x6f, 0x70, 0x61,
            0x00];
        let encoding_raw = create_bej_encoding(&data);
        let encoding = encoding_raw.unwrap();

        let locators = get_locators(vec![], &encoding.tuple);
        assert_eq!(3, locators.len())
    }

    #[test]
    fn test_next_locator() {
        let data: [u8; 34] = [  0x00, 0xf0, 0xf0, 0xf1, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x01,
            0x16, 0x01, 0x01, 0x01, 0x32, 0x00, 0x01, 0x0f, 0x01, 0x01, 0x01,
            0x00, 0x50, 0x01, 0x08, 0x7a, 0x61, 0x6c, 0x6f, 0x6f, 0x70, 0x61,
            0x00];
        let encoding_raw = create_bej_encoding(&data);
        let encoding = encoding_raw.unwrap();

        let locator0 = get_bej_next_locator(&encoding, vec![]).unwrap();
        assert_eq!(locator0, vec![0]);

        let locator1 = get_bej_next_locator(&encoding, locator0).unwrap();
        assert_eq!(locator1, vec![0, 50]);

        let locator2 = get_bej_next_locator(&encoding, locator1).unwrap();
        assert_eq!(locator2, vec![0, 50, 0]);
    }

    #[test]
    fn test_get_val_by_locator() {
        let data: [u8; 34] = [  0x00, 0xf0, 0xf0, 0xf1, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x01,
            0x16, 0x01, 0x01, 0x01, 0x32, 0x00, 0x01, 0x0f, 0x01, 0x01, 0x01,
            0x00, 0x50, 0x01, 0x08, 0x7a, 0x61, 0x6c, 0x6f, 0x6f, 0x70, 0x61,
            0x00];
        let encoding_raw = create_bej_encoding(&data);
        let encoding = encoding_raw.unwrap();
        let bval = get_bej_value_by_locator(&encoding, vec![0, 50]).unwrap();
        match bval {
            BejValue::Set(ref v) => {
                assert_eq!(v[0].seqnum, 0);
                assert_eq!(v.len(), 1);
            },
            _ => assert!(false)
        }
    }

    #[test]
    fn test_decode_version() {
        let data:[u8;4] = [0x00,0xF0,0xF0,0xF1];
        let version_err = parse_bej_version(&data);
        assert_eq!(version_err.is_ok(), true);
        let version = version_err.unwrap();
        assert_eq!(version.major, Some(1));
        assert_eq!(version.medium, Some(0));
        assert_eq!(version.minor, Some(0));
        assert_eq!(version.tiny, None);
    }

    #[test]
    fn test_decode_header() {
        let data: [u8;12] = [0x00,0x00,0x5A,0x00,0x00,0xF1,0xF4,0xF1,0x84,0x07,0x00,0x00];
        let hdr_err = parse_bej_header(&data);
        assert_eq!(hdr_err.is_ok(), true);
        let hdr = hdr_err.unwrap();
        assert_eq!(hdr.version_tag, 0x00);
        assert_eq!(hdr.truncation, false);
        assert_eq!(hdr.entry_count, 90);
        assert_eq!(hdr.version.major, Some(1));
        assert_eq!(hdr.version.medium, Some(4));
        assert_eq!(hdr.version.minor, Some(1));
        assert_eq!(hdr.version.tiny, None);
        assert_eq!(hdr.dict_size, 1924);

    }

    #[test]
    fn test_bej_entry() {
        let example_dict: [u8;141] = [
            0x00, 0x00, 0x06, 0x00, 0xff, 0xff, 0xff, 0xff, 0x8d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x16,
            0x00, 0x04, 0x00, 0x0e, 0x48, 0x00, 0x56, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0c, 0x56, 0x00,
            0x16, 0x01, 0x00, 0x3e, 0x00, 0x01, 0x00, 0x08, 0x62, 0x00, 0x52, 0x02, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x05, 0x6a, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x6f, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4a, 0x6f, 0x62, 0x43, 0x6f, 0x6c, 0x6c, 0x65,
            0x63, 0x74, 0x69, 0x6f, 0x6e, 0x00, 0x44, 0x65, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x69, 0x6f,
            0x6e, 0x00, 0x4d, 0x65, 0x6d, 0x62, 0x65, 0x72, 0x73, 0x00, 0x4e, 0x61, 0x6d, 0x65, 0x00, 0x4f,
            0x65, 0x6d, 0x00, 0x19, 0x43, 0x6f, 0x70, 0x79, 0x72, 0x69, 0x67, 0x68, 0x74, 0x20, 0x32, 0x30,
            0x31, 0x34, 0x2d, 0x32, 0x30, 0x32, 0x30, 0x20, 0x44, 0x4d, 0x54, 0x46, 0x00];

        //0x00, 0x00, 0x00, 0x16, 0x00, 0x04, 0x00, 0x0e, 0x48, 0x00,
        let entry0_wrapped = parse_bej_dict_entry(0, &example_dict);
        assert_eq!(entry0_wrapped.is_ok(), true);
        let entry0 = entry0_wrapped.unwrap();
        assert_eq!(entry0.dbinding, false);
        assert_eq!(entry0.readonly, false);
        assert_eq!(entry0.nullable, false);
        assert_eq!(entry0.seqnum, 0);
        assert_eq!(entry0.children, vec![1,2,3,4]);
        assert_eq!(entry0.name, String::from("JobCollection"));
        assert!(matches!(entry0.format, BejFormat::Set));

        //0x56, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0c, 0x56, 0x00
        let entry1_wrapped = parse_bej_dict_entry(1, &example_dict);
        assert_eq!(entry1_wrapped.is_ok(), true);
        let entry1 = entry1_wrapped.unwrap();
        assert_eq!(entry1.dbinding, false);
        assert_eq!(entry1.readonly, true);
        assert_eq!(entry1.nullable, true);
        assert_eq!(entry1.seqnum, 0);
        assert_eq!(entry1.children, vec![]);
        assert_eq!(entry1.name, String::from("Description"));
        assert!(matches!(entry1.format, BejFormat::String));
    }

    #[test]
    fn test_bej_dict_parse() {
        let example_dict: [u8;141] = [
            0x00, 0x00, 0x06, 0x00, 0xff, 0xff, 0xff, 0xff, 0x8d, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x16, 0x00, 0x04, 0x00, 0x0e, 0x48, 0x00,//0
            0x56, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0c, 0x56, 0x00,//1
            0x16, 0x01, 0x00, 0x3e, 0x00, 0x01, 0x00, 0x08, 0x62, 0x00,//2
            0x52, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05, 0x6a, 0x00,//3
            0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x6f, 0x00,//4
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,//5
            0x4a, 0x6f, 0x62, 0x43, 0x6f, 0x6c, 0x6c, 0x65,//Copyright
            0x63, 0x74, 0x69, 0x6f, 0x6e, 0x00, 0x44, 0x65, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x69, 0x6f,
            0x6e, 0x00, 0x4d, 0x65, 0x6d, 0x62, 0x65, 0x72, 0x73, 0x00, 0x4e, 0x61, 0x6d, 0x65, 0x00, 0x4f,
            0x65, 0x6d, 0x00, 0x19, 0x43, 0x6f, 0x70, 0x79, 0x72, 0x69, 0x67, 0x68, 0x74, 0x20, 0x32, 0x30,
            0x31, 0x34, 0x2d, 0x32, 0x30, 0x32, 0x30, 0x20, 0x44, 0x4d, 0x54, 0x46, 0x00];
        let dict_raw = parse_bej_dict(&example_dict);
        assert_eq!(dict_raw.is_ok(), true);
        let dict = dict_raw.unwrap();
        assert_eq!(dict.entries.len(), 6);
        assert_eq!(dict.version.tiny, Some(15));
        assert_eq!(dict.version.minor, Some(15));
        assert_eq!(dict.version.medium, Some(15));
        assert_eq!(dict.version.major, Some(15));
        assert_eq!(dict.truncation, false);
        assert_eq!(dict.version_tag, 0);

        assert_eq!(dict.entries[0].dbinding, false);
        assert_eq!(dict.entries[0].readonly, false);
        assert_eq!(dict.entries[0].nullable, false);
        assert_eq!(dict.entries[0].seqnum, 0);
        assert_eq!(dict.entries[0].children, vec![1,2,3,4]);
        assert_eq!(dict.entries[0].name, String::from("JobCollection"));
        assert!(matches!(dict.entries[0].format, BejFormat::Set));

        assert_eq!(dict.entries[1].dbinding, false);
        assert_eq!(dict.entries[1].readonly, true);
        assert_eq!(dict.entries[1].nullable, true);
        assert_eq!(dict.entries[1].seqnum, 0);
        assert_eq!(dict.entries[1].children, vec![]);
        assert_eq!(dict.entries[1].name, String::from("Description"));
        assert!(matches!(dict.entries[1].format, BejFormat::String));

        assert_eq!(dict.entries[5].dbinding, false);
        assert_eq!(dict.entries[5].readonly, false);
        assert_eq!(dict.entries[5].nullable, false);
        assert_eq!(dict.entries[5].seqnum, 0);
        assert_eq!(dict.entries[5].children, vec![]);
        assert_eq!(dict.entries[5].name, String::from(""));
        assert!(matches!(dict.entries[5].format, BejFormat::Set));
    }

    #[test]
    fn test_decode_bej() {
        let example_dict: [u8;141] = [
            0x00, 0x00, 0x06, 0x00, 0xff, 0xff, 0xff, 0xff, 0x8d, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x16, 0x00, 0x04, 0x00, 0x0e, 0x48, 0x00,//0
            0x56, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0c, 0x56, 0x00,//1
            0x16, 0x01, 0x00, 0x3e, 0x00, 0x01, 0x00, 0x08, 0x62, 0x00,//2
            0x52, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05, 0x6a, 0x00,//3
            0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x6f, 0x00,//4
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,//5
            0x4a, 0x6f, 0x62, 0x43, 0x6f, 0x6c, 0x6c, 0x65,//Copyright
            0x63, 0x74, 0x69, 0x6f, 0x6e, 0x00, 0x44, 0x65, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x69, 0x6f,
            0x6e, 0x00, 0x4d, 0x65, 0x6d, 0x62, 0x65, 0x72, 0x73, 0x00, 0x4e, 0x61, 0x6d, 0x65, 0x00, 0x4f,
            0x65, 0x6d, 0x00, 0x19, 0x43, 0x6f, 0x70, 0x79, 0x72, 0x69, 0x67, 0x68, 0x74, 0x20, 0x32, 0x30,
            0x31, 0x34, 0x2d, 0x32, 0x30, 0x32, 0x30, 0x20, 0x44, 0x4d, 0x54, 0x46, 0x00];
        let example_coded: [u8; 37] = [
            0x00, 0xF0, 0xF0, 0xF1, 0x00, 0x00, 0x00,
            0x01, 0x00,
            0x00,
            0x01, 0x19,
            0x01, 0x02,
                0x01, 0x00,
                0x50,
                0x01, 0x07,
                0x41, 0x6C, 0x6C, 0x6F, 0x68, 0x61, 0x00,
                0x01, 0x04,
                0x50,
                0x01, 0x06,
                0x42, 0x69, 0x74, 0x63, 0x68, 0x00];
        let dict = parse_bej_dict(&example_dict).unwrap();
        let encoding = create_bej_encoding(&example_coded).unwrap();
        let result = encoding.tuple.decode(&dict, vec![0]).unwrap();
        assert_eq!("\"JobCollection\": {\"Description\": \"Alloha\", \"Name\": \"Bitch\"}", result);
    }
}
