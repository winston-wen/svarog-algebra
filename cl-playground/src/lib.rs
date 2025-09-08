use anyhow::bail;
use memmap2::{Mmap, MmapOptions};
use std::fs::File;
use std::io::Write;
use std::ops::Index;
use std::sync::Arc;

pub struct MmapVecU64 {
    _mmap: Arc<Mmap>, // 保持 mmap 的生命周期
    data: &'static [u64],
}

impl MmapVecU64 {
    pub fn from_file(path: &str) -> anyhow::Result<Self> {
        let file = File::open(path)?;
        let mmap = unsafe { MmapOptions::new().map(&file)? };

        if mmap.len() % std::mem::size_of::<u64>() != 0 {
            bail!("File size is not multiple of sizeof(u64)");
        }

        let len = mmap.len() / std::mem::size_of::<u64>();
        let ptr = mmap.as_ptr() as *const u64;
        let data = unsafe { std::slice::from_raw_parts(ptr, len) };

        let mmap = Arc::new(mmap);

        Ok(MmapVecU64 {
            _mmap: mmap,
            data: unsafe { std::mem::transmute(data) },
        })
    }

    pub fn as_slice(&self) -> &[u64] {
        self.data
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn save_one(val: u64, file: &mut File) -> anyhow::Result<()> {
        let bytes = val.to_le_bytes();
        file.write_all(&bytes)?;
        Ok(())
    }

    pub fn save_many(data: &[u64], file: &mut File) -> anyhow::Result<()> {
        let bytes = unsafe {
            std::slice::from_raw_parts(
                data.as_ptr() as *const u8,
                data.len() * std::mem::size_of::<u64>(),
            )
        };
        file.write_all(bytes)?;
        return Ok(());
    }
}

impl Index<usize> for MmapVecU64 {
    type Output = u64;

    fn index(&self, index: usize) -> &Self::Output {
        &self.as_slice()[index]
    }
}
