#include <elf.h>
#include <fstream>
#include <iostream>

int main() {
  Elf64_Ehdr elf_header{
      // e_ident
      {
          0x7f, 0x45, 0x4c, 0x46, // マジックナンバー
          0x02,                   // 64 ビット
          0x01,                   // 2 の補数、リトルエンディアン
          0x01,                   // ファイルのバージョン
          0x00,                   // UNIX System V ABI
                                  // 残り 8 バイトはゼロ埋め
      },
  };
  elf_header.e_type = 2;       // 実行可能ファイル
  elf_header.e_machine = 0x3e; // AMD x86-64 アーキテクチャ
  elf_header.e_version = 1;
  elf_header.e_entry = 0x400078; // text セグメントの開始位置
  elf_header.e_phoff = sizeof(Elf64_Ehdr); //プログラムヘッダのオフセット
  elf_header.e_shoff = 0; // セクションヘッダのオフセット (使用しないので 0)
  elf_header.e_flags = 0;                   // プロセッサ固有のフラグ
  elf_header.e_ehsize = sizeof(Elf64_Ehdr); // ELF ヘッダのサイズ
  elf_header.e_phentsize = sizeof(Elf64_Phdr); // プログラムヘッダのサイズ
  elf_header.e_phnum = 1; // プログラムヘッダの個数
  elf_header.e_shentsize = sizeof(Elf64_Shdr); // セクションヘッダのサイズ
  elf_header.e_shnum = 0; // セクションヘッダの個数
  elf_header.e_shstrndx = 0; // セクション名文字列テーブルは未定義にしておく

  Elf64_Phdr program_header;
  program_header.p_type = 1;         // プログラムヘッダ
  program_header.p_flags = 7;        // read, write, exec
  program_header.p_offset = 0;       // セグメントのオフセット
  program_header.p_vaddr = 0x400000; // セグメントの仮想アドレス
  program_header.p_paddr = 0x400000; // セグメントの物理アドレス
  program_header.p_filesz = 0x90; // ファイル上のセグメントのサイズ
  program_header.p_memsz = 0x90; // メモリ上のセグメントのサイズ
  program_header.p_align = 0x200000; // セグメントのアライメント

  uint8_t insts[] = {
      0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00, // mov $0x3c, %rax
      0x48, 0x31, 0xff,                         // xor %rdi, %rdi
      0x0f, 0x05,                               // syscall
  };

  std::ofstream out_file("bin", std::ios::out | std::ios::binary);
  out_file.write((char *)&elf_header, sizeof(elf_header));
  out_file.write((char *)&program_header, sizeof(program_header));
  out_file.write((char *)&insts, sizeof(insts));
  out_file.close();

  std::cout << "Complete" << std::endl;
  return EXIT_SUCCESS;
}
