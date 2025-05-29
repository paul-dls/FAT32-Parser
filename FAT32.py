#!/usr/bin/python3

# Authors ---------------------------------------------------------#
#  Younes Tasra ~ https://younestasra-r4z3rsw0rd.github.io/        #
#  Ayman Zerda  ~ https://aymanzerda-sudotime.github.io/           #
#------------------------------------------------------------------#

# Built-in Python Libraries:
from time import sleep
import argparse
import sys
import csv
import re
import traceback
import binascii

# Third Party Python Libraries
from termcolor import colored
from colorama import Fore, Style
from prettytable import PrettyTable


SECTOR_SIZE = 512
MASTER_BOOT_CODE_LENGTH = 446
PARTITION_TABLES_LENGTH = 16
BOOT_SIGNATURE_LENGTH = 2
BOOT_SECTOR_START = 0
FSINFO_SECTOR_START = 0
BOOT_SECTOR_SIZE = 512

# Filesystems:
FILE_SYSTEMS = {
    "01": "FAT12",
    "04": "FAT16",
    "05": "MS Extended partition using CHS",
    "06": "FAT16B",
    "07": "NTFS, HPFS, exFAT",
    "0B": "FAT32 CHS",
    "0C": "FAT32 LBA",
    "0E": "FAT16 LBA",
    "0F": "MS Extended partition LBA",
    "42": "Windows Dynamic Volume",
    "82": "Linux Swap",
    "83": "Linux Native File System (ext2/3/4, JFS, Reiser, xiafs, and others)",
    "84": "Windows Hibernation Partition",
    "85": "Linux Extended",
    "8E": "Linux LVM",
    "A5": "FreeBSD Slice",
    "A6": "OpenBSD Slice",
    "AB": "Mac OS X boot",
    "AF": "HFS, HFS+",
    "EE": "MS GPT",
    "EF": "Intel EFI",
    "FB": "VMware VMFS",
    "FC": "VMware Swap",
    }
          # Others: https://thestarman.pcministry.com/asm/mbr/PartTypes.htm

PREDEFINED_VALUES = {
   "Boot_Flag": ["Bootable", "NOT Bootable"],
   "BytesPerSector": [0, 512, 1024, 2048, 4096],
   "SectorsPerCluster": [1, 2, 4, 8, 16, 32, 64, 128],
   "ClusterSize": 32768,                                    # Must be 32 KB or smaller
   "ReservedSectors": 32,                                   # FAT32 uses 32 (check if the number of reserved sectors is smaller greater than 32)
   "NrRootDirEntries": 0,                                   # Must be 0
   "SectorsPerFilesystem": 0,                               # Must be 0
   "MediaType": ['f8', 'f0'],
   "SectorsPerFat": 0,                                      # Must be 0
   "ExtendedBootSignature": "29",
   "FileSystemLabel": "FAT32   ",
   "BootSectorSignature": "aa55",
   "FSINFO_Signature1": "41615252",
   "FSINFO_Signature2": "61417272",
   "FSINFOSector_Signature": "aa550000",
}

# Initializing global variables: 
Partitions_StartingSector = []    # Saving Partitons Starting Sector values for later use.
FSINFO_StartingSector = {}        # Saving FSINFO Starting Sector values for later use.

# Printing messages with context:
def print_message(message, type):
    if type == 'SUCCESS':
        print('[' + colored('+', 'green') +  '] ' + message)    # Success
    elif type == 'INFO':
        print('[' + colored('*', 'blue') +  '] ' + message)     # Info
    elif type == 'WARNING':
        print('[' + colored('!', 'yellow') +  '] ' + message)   # Warning
    elif type == 'ALERT':
        print('[' + colored('!!', 'yellow') +  '] ' + message)  # Alert
    elif type == 'ERROR':
        print('[' + colored('-', 'red') +  '] ' + message)      # Error

# Printing Documentation:
def print_docs(message, byte_range, size, essential=None, show_docs = True):
   if show_docs:
      if (essential == "yes"):
         if (size == 1) :
            print("\t" + Style.BRIGHT + Fore.WHITE + "[" + Fore.GREEN + "ESSENTIAL" + Fore.WHITE + "] " + "[" + Fore.MAGENTA + byte_range + Fore.WHITE + "] " + Fore.YELLOW + message + Fore.WHITE + ' (' + Fore.CYAN + str(size) + " byte" + Fore.WHITE + ')' + Style.NORMAL + Fore.WHITE + "\n")
         else:
            print("\t" + Style.BRIGHT + Fore.WHITE + "[" + Fore.GREEN + "ESSENTIAL" + Fore.WHITE + "] " + "[" + Fore.MAGENTA + byte_range + Fore.WHITE + "] " + Fore.YELLOW + message + Fore.WHITE + ' (' + Fore.CYAN + str(size) + " bytes" + Fore.WHITE + ')' + Style.NORMAL + Fore.WHITE + "\n")
      elif essential == "no":
         if (size == 1) :
            print("\t" + Style.BRIGHT + Fore.WHITE + "[" + Fore.RED + "NOT ESSENTIAL" + Fore.WHITE + "] " + "[" + Fore.MAGENTA + byte_range + Fore.WHITE + "] " + Fore.YELLOW + message + Fore.WHITE + ' (' + Fore.CYAN + str(size) + " byte" + Fore.WHITE + ')' + Style.NORMAL + Fore.WHITE + "\n")
         else:
            print("\t" + Style.BRIGHT + Fore.WHITE + "[" + Fore.RED + "NOT ESSENTIAL" + Fore.WHITE + "] " + "[" + Fore.MAGENTA + byte_range + Fore.WHITE + "] " + Fore.YELLOW + message + Fore.WHITE + ' (' + Fore.CYAN + str(size) + " bytes" + Fore.WHITE + ')' + Style.NORMAL + Fore.WHITE + "\n")
      else:
         if (size == 1) :
            print("\t" + Style.BRIGHT + Fore.WHITE + "[" + Fore.MAGENTA + byte_range + Fore.WHITE + "] " + Fore.YELLOW + message + Fore.WHITE + ' (' + Fore.CYAN + str(size) + " byte" + Fore.WHITE + ')' + Style.NORMAL + Fore.WHITE + "\n")
         else:
            print("\t" + Style.BRIGHT + Fore.WHITE + "[" + Fore.MAGENTA + byte_range + Fore.WHITE + "] " + Fore.YELLOW + message + Fore.WHITE + ' (' + Fore.CYAN + str(size) + " bytes" + Fore.WHITE + ')' + Style.NORMAL + Fore.WHITE + "\n")

# Raw to Hex image converter:
def raw2hex(image_path, data=None, start=None):
    with open(image_path, 'rb') as f:
        if data is None and start is None:
            raw_data = f.read() 
        elif start is None:
            raw_data = f.read(data)
        elif data is not None and data is not None:
           f.seek(start)
           raw_data = f.read(data)

    return raw_data.hex()

# ----------------------------------------- #
# Analysis of the Master Boot Record - MBR  #
# ----------------------------------------- #

# Checking the state of partitions (Bootable/Non-Bootable)
def bootable(hex_image, partition_counter):
    if hex_image[MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter:MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+2] == "80" :
      return "Bootable"
    elif hex_image[MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter:MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+2] == "00" : 
       return "NOT Bootable"
    else:
      return "NOT Defined"

def startingSector_CHS(hex_image, partition_counter):
   return hex_image[MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+2:MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+8]

def fileSys(hex_image, partition_counter):
   for key in FILE_SYSTEMS:
      if (str(hex_image[MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+8:MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+10]) == str(key).lower()) :
         return FILE_SYSTEMS[key]
   
   return "Unknown (0x" + str(hex_image[MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+8:MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+10]) + ")"
   

def endingSector_CHS(hex_image, partition_counter):
   return hex_image[MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+10:MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+16]

def startingSector_LBA(hex_image, partition_counter):
   # Start Sector value in little endian format
   hex_value = hex_image[MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+16:MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+24]

   # Convert to big endian format and remove leading zeros
   start_sector = bytes.fromhex(hex_value)
   start_sector = start_sector[::-1].hex().lstrip('0')

   # Add a zero if the result is an empty string
   if not start_sector:
      start_sector = '0'

   return int(start_sector, 16)

def totalSectors(hex_image, partition_counter):
   
   hex_value = hex_image[MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+24:MASTER_BOOT_CODE_LENGTH*2+PARTITION_TABLES_LENGTH*2*partition_counter+32]
   total_sectors = bytes.fromhex(hex_value)
   total_sectors = total_sectors[::-1].hex().lstrip('0')
   if not total_sectors:
      total_sectors = '0'

   return total_sectors

def MBRSignature(hex_image):
   little_endian = hex_image[-4:]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return value

# ----------------------------- #
# Analysis of the Boot Sector   #
# ----------------------------- #

def jumpCode(hex_image) :
   # Size: 3 Bytes
   little_endian = hex_image[BOOT_SECTOR_START:BOOT_SECTOR_START+3*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()
   return value      # Hexadecimal value in little endian format.

def oem(hex_image) :
   # Size: 8 Bytes
   jumpCode = 3*2
   hex_bytes = bytes.fromhex(hex_image[BOOT_SECTOR_START+jumpCode:BOOT_SECTOR_START+jumpCode+8*2])

   return hex_bytes.decode('ascii')

def bytesPerSector(hex_image):
   # Size: 2 bytes
   start = 11*2         # JumpCode + OEM
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)   # Apply some checks on this value

def sectorsPerCluster(hex_image) :
   # Size: 1 byte
   start = 13*2         # JumpCode + OEM + BytesPerSector
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+1*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)   # Apply some checks on this value

def reservedArea(hex_image): # Reserved Clusters
   # size: 2 bytes
   start = 14*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)

def numOfFAT(hex_image):
   # Size: 1 byte
   start = 16*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+1*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)

def numOfRootDirEntries(hex_image):
   # Size: 2 bytes
   start = 17*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      # Apply some checks on this value (Always == 0 for FAT32)

def numOfSectors(hex_image):
   # Size: 2 bytes
   start = 19*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      # Apply some checks on this value (Always == 0 for FAT32)

def mediaType(hex_image):
   # Size: 1 byte
   start = 21*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors
   value = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+1*2]  
   return value      # Apply some checks on this value. Only 2 values are supported (0xF8 and 0xF0)

def FATSize(hex_image) :
   # Size: 2 bytes
   start = 22*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      # Apply some checks on this value (Always == 0 for FAT32)

def numOfSectorsPerTrack(hex_image) :
   # Size: 2 bytes
   start = 24*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FATSize
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      
def numOfHeads(hex_image) :
   # Size: 2 bytes
   start = 26*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      

def numOfHiddenSectors(hex_image) :
   # Size: 4 bytes
   start = 28*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+4*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      # Apply some checks on this value

def totalNumberOfSectors(hex_image) :  # Number of Sectors in the entire disk
   # Size: 4 bytes
   start = 32*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+4*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      # Apply some checks on this value

# --------------------------------------------------------------- #
# Analysis of what's after the first 36 bytes of the boot sector  #
# --------------------------------------------------------------- #
def numOfSectorsPerFAT(hex_image):
   # Size: 4 bytes
   start = 36*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+4*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      # Apply some checks on this value

def Flags(hex_image):
   # Size: 2 bytes
   start = 40*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   hex_value = big_endian[::-1].hex()
   int_value = int(hex_value, 16) 
   bits = format(int_value, '0{}b'.format(len(hex_value)*4))  # convert integer to binary string with leading zero
   pretty_bits = ' '.join(bits[i:i+4] for i in range(0, len(bits), 4))
   return pretty_bits    # If bit 7 is 1, only one of the FAT structures is active and its index is described in bits 0–3. Otherwise, all FAT structures are mirrors of each other.

'''
Bits 0-3: number of active FAT (if bit 7 is 1)
Bits 4-6: reserved
Bit 7: one: single active FAT; zero: all FATs are updated at runtime
Bits 8-15: reserved
'''

def FAT32_version(hex_image):
   # Size: 2 bytes
   start = 42*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT + Flags
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      # Apply some checks on this value => Low bytes means MINOR VERSION and High bytes means MAJOR VERSION

def RootDirClusterNumber(hex_image) :  # Cluster Number of the Start of the Root Directory
   # Size: 4 bytes
   start = 44*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT + Flags + FAT32Version
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+4*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      # Apply some checks on this value

def FSINFOSectorNumber(hex_image) :  # Sector where FSINFO (File System Information Sector) structure can be found
   # Size: 2 bytes
   start = 48*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT + Flags + FAT32Version + RootDirectoryClusterNumber
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      # Apply some checks on this value

def BackupBootSector(hex_image):    # Sector where backup copy of boot sector is located (Default is 6)
   # Size: 2 bytes
   start = 50*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT + Flags + FAT32Version + RootDirectoryClusterNumber + FSINFOSectorNumber
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)      # Apply some checks on this value

# .... SKIPPING 12 BYTES OF RESERVED AREA ....

def BIOSDriveNumber(hex_image) :
   # Size: 1 byte
   start = 64*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT + Flags + FAT32Version + RootDirectoryClusterNumber + FSINFOSectorNumber + BackupBootSector + 12 + 
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+1*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16) 

# .... SKIPPING 1 BYTE UNUSED ....

def extendedBootSignature(hex_image) :
   # Size: 1 byte
   start = 66*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT + Flags + FAT32Version + RootDirectoryClusterNumber + FSINFOSectorNumber + BackupBootSector + 12 + BIOSDriveNumber + 1 
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+1*2] 
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()
   return value   # Apply some check on this value (Default is 0x29)

def partitionSerialNumber(hex_image) :
   # Size: 4 bytes
   start = 67*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT + Flags + FAT32Version + RootDirectoryClusterNumber + FSINFOSectorNumber + BackupBootSector + 12 + BIOSDriveNumber + 1 + ExtendedBootSignature
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+4*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16) 

def volumeName(hex_image): 
   # Size: 11 bytes
   start = 71*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT + Flags + FAT32Version + RootDirectoryClusterNumber + FSINFOSectorNumber + BackupBootSector + 12 + BIOSDriveNumber + 1 + ExtendedBootSignature + PartitionSerialNumber
   hex_bytes = bytes.fromhex(hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+11*2])

   return hex_bytes.decode('ascii')

def FileSystemType(hex_image):
   # Size: 8 bytes
   start = 82*2         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT + Flags + FAT32Version + RootDirectoryClusterNumber + FSINFOSectorNumber + BackupBootSector + 12 + BIOSDriveNumber + 1 + ExtendedBootSignature + PartitionSerialNumber + VolumeNameOfPartition
   hex_bytes = bytes.fromhex(hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+8*2])

   return hex_bytes.decode('ascii')

# .... SKIPPING 420 Bytes of Executable Code

def BootRecordSignature_1(hex_image):
   # Size: 2 bytes         # JumpCode + OEM + BytesPerSector + SectorsPerCluster + reservedArea + numberOfFATs + NumberOfRootDirectoryEntries + NumberOfSectors + MediaType + FatSize + NumberOfSectorsPerTrack + NumberOfHeads + NumberOfHiddenSectors + NumberOfSectorsInPartition + NumberOfSectorsPerFAT + Flags + FAT32Version + RootDirectoryClusterNumber + FSINFOSectorNumber + BackupBootSector + 12 + BIOSDriveNumber + 1 + ExtendedBootSignature + PartitionSerialNumber + VolumeNameOfPartition + FileSystemType + 420 
   start = 510*2
   little_endian = hex_image[BOOT_SECTOR_START+start:BOOT_SECTOR_START+start+2*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()
   return value  # Apply some checks on this value.(Always == 55 AA)

# --------------------------------------------------- #
# Analysis of File System Information Sector (FSINFO) #
# --------------------------------------------------- #

def FSINFOSignature_1(hex_image):
   # Size: 4 bytes 
   little_endian = hex_image[FSINFO_SECTOR_START:FSINFO_SECTOR_START+4*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()
   return value

# .... SKIPPING UNUSED 480 Bytes ....

def FSINFOSignature_2(hex_image):
   # Size: 4 bytes 
   start = 484*2           # This is the unused 480 bytes we skipped earlier + FirstSignature
   little_endian = hex_image[FSINFO_SECTOR_START+start:FSINFO_SECTOR_START+start+4*2] 
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()
   return value

def NumOfFreeClusters(hex_image): 
   # Size: 4 bytes
   start = 488*2           # FirstSignature + 480 + SecondSignature
   little_endian = hex_image[FSINFO_SECTOR_START+start:FSINFO_SECTOR_START+start+4*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)   # Set to 1 if unknown number

def NextFreeClusterSectorNumber(hex_image): 
   # Size: 4 bytes
   start = 492*2           # FirstSignature + 480 + SecondSignature + NumberOfFreeClusters
   little_endian = hex_image[FSINFO_SECTOR_START+start:FSINFO_SECTOR_START+start+4*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()

   return int(value, 16)

# .... SKIPPING UNUSED 12 Bytes ....

def FsinfoSectorSignature(hex_image) :
   # Size: 4 bytes
   start = 508*2           # FirstSignature + 480 + SecondSignature + NumberOfFreeClusters + NextFreeClusterSectorNumber + 12 
   little_endian = hex_image[FSINFO_SECTOR_START+start:FSINFO_SECTOR_START+start+4*2]
   big_endian = bytes.fromhex(little_endian)
   value = big_endian[::-1].hex()
   return value  # Apply Some checks here !!




# --------------------------------------------------- #
# Analysis of the directory entries #
# --------------------------------------------------- #

def getDirectoryEntry(hex_image, sector_number, entry_number):
   
   bytes_per_sector = bytesPerSector(hex_image)
   sectors_per_cluster = sectorsPerCluster(hex_image)

   start = 2 * bytes_per_sector * sector_number * sectors_per_cluster + entry_number * 32*2
   print("start: ", start)
   end = start + 32*2
   if hex_image[start:end] == "":
      print("empty")
   return(hex_image[start:end])


# --------------------------------------------------- #
# Parsers
# --------------------------------------------------- #


def parseMasterBootRecord(args, image):

   table = PrettyTable()
   table1 = PrettyTable()
   table2 = PrettyTable()
   table3 = PrettyTable()
   table4 = PrettyTable()

   table.field_names = ["", "Bootable", "Start Head", "Start Sector", "Start Cylinder", "File System", "End Head", "End Sector", "End Cylinder", "Start Sector (LBA)", "Number of Sectors", "Size (KB)"]
   table1.field_names = ["", "Bootable", "Start Head", "Start Sector", "Start Cylinder", "File System", "End Head", "End Sector", "End Cylinder", "Start Sector (LBA)", "Number of Sectors", "Size (KB)"]
   table2.field_names = ["", "Bootable", "Start Head", "Start Sector", "Start Cylinder", "File System", "End Head", "End Sector", "End Cylinder", "Start Sector (LBA)", "Number of Sectors", "Size (KB)"]
   table3.field_names = ["", "Bootable", "Start Head", "Start Sector", "Start Cylinder", "File System", "End Head", "End Sector", "End Cylinder", "Start Sector (LBA)", "Number of Sectors", "Size (KB)"]
   table4.field_names = ["", "Bootable", "Start Head", "Start Sector", "Start Cylinder", "File System", "End Head", "End Sector", "End Cylinder", "Start Sector (LBA)", "Number of Sectors", "Size (KB)"]

   
   FoundFileSystems = []             # Saving found filesystems for later use.
   partition_counter = 0             # Keeping track of how many partition has been parsed
   check = 0                         # Checking how many partition is bootable

   
   print("")
   print_message("Starting Parsing Of " + Fore.MAGENTA + "Master Boot Record :" + Style.NORMAL + Fore.WHITE, 'SUCCESS')
   print("--------------------------------------------\n")
   sleep(1)

   print_message("Bootstrap Code located in the first 446 bytes of the first 512-byte sector (MBR)", 'INFO')
   print("")
   print_docs("This area contains the code that is executed when the computer starts up. It is responsible for loading the operating system and is typically written by the operating system vendor.", "0-445", 446, show_docs = args.verbose)
   start = 446
   while True:
      print(Style.BRIGHT + Fore.GREEN + "==> " + Fore.WHITE + "Partition n°" + Fore.CYAN + str(partition_counter+1) + Style.NORMAL + Fore.WHITE)
      print("")
      if bootable(image, partition_counter) == "Bootable":
         print_message("Bootable Flag: " + Style.BRIGHT + Fore.CYAN + "0x80" + Style.NORMAL + Fore.WHITE + " => Partition {}".format(Style.BRIGHT +Fore.MAGENTA + str(partition_counter+1)) + Style.NORMAL + Fore.WHITE + " is " + Style.BRIGHT +  Fore.GREEN + "Bootable" + Style.NORMAL + Fore.WHITE, 'INFO')
      elif bootable(image, partition_counter) == "NOT Bootable":
         print_message("Bootable Flag: " + Style.BRIGHT + Fore.CYAN + "0x00" + Style.NORMAL + Fore.WHITE + " => Partition {}".format(Style.BRIGHT +Fore.MAGENTA + str(partition_counter+1)) + Style.NORMAL + Fore.WHITE + " is " + Style.BRIGHT + Fore.RED + "NOT Bootable" + Style.NORMAL + Fore.WHITE, 'INFO')
      else: # Checking the bootable flag:
         print("\t", end='')
         print_message(f'The Bootable Flag value is invalid !!', 'ALERT')

      print_docs("Only two values are allowed: 0x80 means that the partition is bootable & 0x00 means that the partition is not bootable.", f"{str(start)}-{str(start)}", 1, show_docs = args.verbose)
      print_message("Start Head: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + startingSector_CHS(image, partition_counter)[0:2])+ Style.NORMAL + Fore.WHITE, 'INFO')

      print_docs("The head number specifies which of the disk's platters the sector is located on", f"{str(start+1)}-{str(start+1)}", 1, show_docs = args.verbose)
      print_message("Start Sector: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + startingSector_CHS(image, partition_counter)[2:4])+ Style.NORMAL + Fore.WHITE, 'INFO')

      print_docs("The sector number specifies which sector on the track the partition begins.", f"{str(start+2)}-{str(start+2)}", 1, show_docs = args.verbose)
      print_message("Start Cylinder: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + startingSector_CHS(image, partition_counter)[4:6])+ Style.NORMAL + Fore.WHITE, 'INFO')

      print_docs("The cylinder number specifies which cylinder the partition begins on.", f"{str(start+3)}-{str(start+3)}", 1, show_docs = args.verbose)
      print_message("File System: {}".format(Fore.GREEN + Style.BRIGHT + fileSys(image, partition_counter)) + Style.NORMAL + Fore.WHITE, 'INFO')
      FoundFileSystems.append(fileSys(image, partition_counter))

      print_docs("The partition type field identifies the file system type that should be in the partition.", f"{str(start+4)}-{str(start+4)}", 1, show_docs = args.verbose)
      print_message("End Head: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + endingSector_CHS(image, partition_counter)[0:2])+ Style.NORMAL + Fore.WHITE, 'INFO')

      print_docs("The ending head value indicates the head number of the last sector in the partition.", f"{str(start+5)}-{str(start+5)}", 1, show_docs = args.verbose)
      print_message("End Sector: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + endingSector_CHS(image, partition_counter)[2:4])+ Style.NORMAL + Fore.WHITE, 'INFO')

      print_docs("The ending sector value represents the sector number of the last sector in the partition.", f"{str(start+6)}-{str(start+6)}", 1, show_docs = args.verbose)
      print_message("End Cylinder: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + endingSector_CHS(image, partition_counter)[4:6])+ Style.NORMAL + Fore.WHITE, 'INFO')

      print_docs("The ending cylinder value represents the cylinder number of the last sector in the partition", f"{str(start+7)}-{str(start+7)}", 1, show_docs = args.verbose)
      print_message("The starting sector of partition {}: {}".format(partition_counter+1, Fore.GREEN + Style.BRIGHT + str(startingSector_LBA(image, partition_counter)))+ Style.NORMAL + Fore.WHITE, 'INFO')

      print_docs("A 32-bit value that specifies the first sector of the partition relative to the beginning of the disk.", f"{str(start+8)}-{str(start+11)}", 4, show_docs = args.verbose)
      print_message("Partition {} contains {} sector".format(partition_counter+1, Fore.GREEN + Style.BRIGHT + str(int(totalSectors(image, partition_counter), 16)))+ Style.NORMAL + Fore.WHITE, 'INFO')
      print_message("Partition size: {} Bytes ≃ {} KB".format(Fore.GREEN + Style.BRIGHT + str(int(totalSectors(image, partition_counter), 16)*512) , round(int(totalSectors(image, partition_counter), 16)*512/1024))+ Style.NORMAL + Fore.WHITE + "\n", 'INFO')

      print_docs("A 32-bit value that specifies the size of the partition in sectors.", f"{str(start+12)}-{str(start+15)}", 4, show_docs = args.verbose)
      
      if (partition_counter == 0) :
         table1.add_row( ["Partition {}".format(partition_counter+1), bootable(image, partition_counter), "0x" + startingSector_CHS(image, partition_counter)[0:2], "0x" + startingSector_CHS(image, partition_counter)[2:4], "0x" + startingSector_CHS(image, partition_counter)[4:6], fileSys(image, partition_counter), "0x" + endingSector_CHS(image, partition_counter)[0:2], "0x" + endingSector_CHS(image, partition_counter)[2:4], "0x" + endingSector_CHS(image, partition_counter)[4:6], startingSector_LBA(image, partition_counter), int(totalSectors(image, partition_counter), 16), round(int(totalSectors(image, partition_counter), 16)*512/1024)])
         table.add_row( ["Partition {}".format(partition_counter+1), bootable(image, partition_counter), "0x" + startingSector_CHS(image, partition_counter)[0:2], "0x" + startingSector_CHS(image, partition_counter)[2:4], "0x" + startingSector_CHS(image, partition_counter)[4:6], fileSys(image, partition_counter), "0x" + endingSector_CHS(image, partition_counter)[0:2], "0x" + endingSector_CHS(image, partition_counter)[2:4], "0x" + endingSector_CHS(image, partition_counter)[4:6], startingSector_LBA(image, partition_counter), int(totalSectors(image, partition_counter), 16), round(int(totalSectors(image, partition_counter), 16)*512/1024)])
         print(Style.BRIGHT + "[" + Fore.GREEN + "+" + Fore.WHITE + "] " + "Partition Table Entry " + Fore.GREEN + "#1" + Style.NORMAL + Fore.WHITE)
         print(table1)
         print("")
      if (partition_counter == 1) :
         table2.add_row( ["Partition {}".format(partition_counter+1), bootable(image, partition_counter), "0x" + startingSector_CHS(image, partition_counter)[0:2], "0x" + startingSector_CHS(image, partition_counter)[2:4], "0x" + startingSector_CHS(image, partition_counter)[4:6], fileSys(image, partition_counter), "0x" + endingSector_CHS(image, partition_counter)[0:2], "0x" + endingSector_CHS(image, partition_counter)[2:4], "0x" + endingSector_CHS(image, partition_counter)[4:6], startingSector_LBA(image, partition_counter), int(totalSectors(image, partition_counter), 16), round(int(totalSectors(image, partition_counter), 16)*512/1024)])
         table.add_row( ["Partition {}".format(partition_counter+1), bootable(image, partition_counter), "0x" + startingSector_CHS(image, partition_counter)[0:2], "0x" + startingSector_CHS(image, partition_counter)[2:4], "0x" + startingSector_CHS(image, partition_counter)[4:6], fileSys(image, partition_counter), "0x" + endingSector_CHS(image, partition_counter)[0:2], "0x" + endingSector_CHS(image, partition_counter)[2:4], "0x" + endingSector_CHS(image, partition_counter)[4:6], startingSector_LBA(image, partition_counter), int(totalSectors(image, partition_counter), 16), round(int(totalSectors(image, partition_counter), 16)*512/1024)])
         print(Style.BRIGHT + "[" + Fore.GREEN + "+" + Fore.WHITE + "] " + "Partition Table Entry " + Fore.GREEN + "#2" + Style.NORMAL + Fore.WHITE)
         print(table2)
         print("\n")
      if (partition_counter == 2) :
         table3.add_row( ["Partition {}".format(partition_counter+1), bootable(image, partition_counter), "0x" + startingSector_CHS(image, partition_counter)[0:2], "0x" + startingSector_CHS(image, partition_counter)[2:4], "0x" + startingSector_CHS(image, partition_counter)[4:6], fileSys(image, partition_counter), "0x" + endingSector_CHS(image, partition_counter)[0:2], "0x" + endingSector_CHS(image, partition_counter)[2:4], "0x" + endingSector_CHS(image, partition_counter)[4:6], startingSector_LBA(image, partition_counter), int(totalSectors(image, partition_counter), 16), round(int(totalSectors(image, partition_counter), 16)*512/1024)])
         table.add_row( ["Partition {}".format(partition_counter+1), bootable(image, partition_counter), "0x" + startingSector_CHS(image, partition_counter)[0:2], "0x" + startingSector_CHS(image, partition_counter)[2:4], "0x" + startingSector_CHS(image, partition_counter)[4:6], fileSys(image, partition_counter), "0x" + endingSector_CHS(image, partition_counter)[0:2], "0x" + endingSector_CHS(image, partition_counter)[2:4], "0x" + endingSector_CHS(image, partition_counter)[4:6], startingSector_LBA(image, partition_counter), int(totalSectors(image, partition_counter), 16), round(int(totalSectors(image, partition_counter), 16)*512/1024)])
         print(Style.BRIGHT + "[" + Fore.GREEN + "+" + Fore.WHITE + "] " + "Partition Table Entry " + Fore.GREEN + "#3" + Style.NORMAL + Fore.WHITE)
         print(table3)
         print("\n")
      if (partition_counter == 3) :
         table4.add_row( ["Partition {}".format(partition_counter+1), bootable(image, partition_counter), "0x" + startingSector_CHS(image, partition_counter)[0:2], "0x" + startingSector_CHS(image, partition_counter)[2:4], "0x" + startingSector_CHS(image, partition_counter)[4:6], fileSys(image, partition_counter), "0x" + endingSector_CHS(image, partition_counter)[0:2], "0x" + endingSector_CHS(image, partition_counter)[2:4], "0x" + endingSector_CHS(image, partition_counter)[4:6], startingSector_LBA(image, partition_counter), int(totalSectors(image, partition_counter), 16), round(int(totalSectors(image, partition_counter), 16)*512/1024)])
         table.add_row( ["Partition {}".format(partition_counter+1), bootable(image, partition_counter), "0x" + startingSector_CHS(image, partition_counter)[0:2], "0x" + startingSector_CHS(image, partition_counter)[2:4], "0x" + startingSector_CHS(image, partition_counter)[4:6], fileSys(image, partition_counter), "0x" + endingSector_CHS(image, partition_counter)[0:2], "0x" + endingSector_CHS(image, partition_counter)[2:4], "0x" + endingSector_CHS(image, partition_counter)[4:6], startingSector_LBA(image, partition_counter), int(totalSectors(image, partition_counter), 16), round(int(totalSectors(image, partition_counter), 16)*512/1024)])
         print(Style.BRIGHT + "[" + Fore.GREEN + "+" + Fore.WHITE + "] " + "Partition Table Entry " + Fore.GREEN + "#4" + Style.NORMAL + Fore.WHITE)
         print(table4)
         print("\n")

      start += 16
      if (bootable(image, partition_counter) == "Bootable") :
         check += 1

      Partitions_StartingSector.append(startingSector_LBA(image, partition_counter))
      partition_counter += 1
      if (partition_counter == 4) :
         print_message("Boot signature: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + str(MBRSignature(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')
         print("")
         
         # Checking the boot signature value:
         if (MBRSignature(image) != PREDEFINED_VALUES["BootSectorSignature"]):
            print("\t", end='')
            print("The boot signature is invalid. It should be 0xAA55")
         if (check != 0) :
            if (check == 1) :
               print_message("{} partition is ".format(check) + Fore.CYAN + "Bootable" + Fore.WHITE,'SUCCESS')
               print_message("{} partitions are ".format(partition_counter-check) + Fore.RED + "NOT Bootable" + Fore.WHITE + "\n", 'SUCCESS')
            else:
               print_message("{} partitions are ".format(check) + Fore.CYAN + "Bootable" + Fore.WHITE, 'SUCCESS')
               print_message("{} partitions are ".format(partition_counter-check) + Fore.RED + "NOT Bootable" + Fore.WHITE + "\n", 'SUCCESS')
         else :
            print_message(Style.BRIGHT + Fore.YELLOW + "None of the partitions is bootable." + Fore.WHITE, 'WARNING')
         print(table)
         break 

   cnt = 0
   for element in FoundFileSystems:
      if 'FAT32' in element:
         cnt += 1

   # Stop the program if --mbr option is enabled or if the filesystem is not FAT32
   if (args.mbr or cnt == 0) :
      sys.exit()

   print("\n")




def parseBootSector(args, image, partition_number):

   
      
   print_message("Parsing" + Fore.MAGENTA + " Boot Sector" + Fore.WHITE + " of Partition {} :".format(Style.BRIGHT + Fore.CYAN + str(partition_number+1) + Style.NORMAL + Fore.WHITE), 'SUCCESS')
   print("---------------------------------------\n")
   sleep(1)
   print_message("Jump Code Instructions: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + str(jumpCode(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                               # 0x9058EB  JMP xxxx NOP
   
   print_docs(f"Assembly instruction to jump to boot code: JMP + NOP.", "0-2", 3, "no", show_docs = args.verbose)
   print_message("OEM Name: {}".format(Fore.GREEN + Style.BRIGHT + oem(image))+ Style.NORMAL + Fore.WHITE, 'INFO')                                                              # MSDOS5.0
   
   print_docs("OEM Name+version in Ascii.", "3-10", 8, "no", show_docs = args.verbose)
   print_message("The size of each sector in bytes: {}".format(Fore.GREEN + Style.BRIGHT + str(bytesPerSector(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                            # 512 (Must be one of 512, 1024, 2048, 4096)
   
   # Checking the size value of each sector: 
   if bytesPerSector(image) not in PREDEFINED_VALUES["BytesPerSector"]:
      print("\t", end="")
      print_message(f'This sector size value is invalid !!', 'WARNING')
   
   print_docs("Allowed values include 512, 1024, 2048, 4096.", "11-12", 2, "yes", show_docs = args.verbose)
   print_message("Number of Sectors Per cluster: {}".format(Fore.GREEN + Style.BRIGHT + str(sectorsPerCluster(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                      # 8 (Must be one of 1, 2, 4, 8, 16, 32, 64, 128.) 
   
   # Checking the number of sectors per cluster:
   if sectorsPerCluster(image) not in PREDEFINED_VALUES["SectorsPerCluster"]:
      print("\t", end='')
      print_message(f'The number of sectors per cluster is invalid !!', 'WARNING')
   
   print_docs("Allowed values are powers of 2, but the cluster size must be 32KB or smaller.", "13-13", 1, "yes", show_docs = args.verbose)
   print_message("The size of each Cluster in Bytes: {}".format(Fore.GREEN + Style.BRIGHT + str(sectorsPerCluster(image)*bytesPerSector(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')  # 4096  (A cluster should have at most 32768 bytes. In rare cases 65536 is OK.)
   
   # Checking the cluster size value:
   if sectorsPerCluster(image)*bytesPerSector(image) > 32768:
      print("\t", end='')
      print_message(f'This cluster size is invalid !! It should be lesser than or equal to 32KB (KiloBytes)', 'WARNING')
   print_message("Number of Reserved Sectors: {}".format(Fore.GREEN + Style.BRIGHT + str(reservedArea(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                              # 36 (FAT12 and FAT16 use 1. FAT32 uses 32 reserved sector and leaves 4 aside)
   
   # Checking the number of reserved sectors:
   if reservedArea(image) < PREDEFINED_VALUES["ReservedSectors"]:
      print("\t", end='')
      print_message(f'The number of reserved sectors is invalid !! It should be greater than or equal to 32', 'WARNING')
   
   print_docs("Size in sectors of the reserved area. FAT32 uses 32 reserved sector.", "14-15", 2, "yes", show_docs = args.verbose)
   print_message("Number of FAT copies: {}".format(Fore.GREEN + Style.BRIGHT + str(numOfFAT(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                                        # 2  (Typically two for redundancy, but according to Microsoft it can be one for some small storage devices.)
   
   print_docs("Typically two for redundancy, but according to Microsoft it can be one for some small storage devices.", "16-16", 1, "yes", show_docs = args.verbose)
   print_message("Number of Root directory entries: {}".format(Fore.GREEN + Style.BRIGHT + str(numOfRootDirEntries(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                 # 0  (Always 0 for FAT32)
   
   # Checking the number of root directory enties:
   if numOfRootDirEntries(image) != PREDEFINED_VALUES["NrRootDirEntries"]:
      print("\t", end='')
      print_message(f'The number of root directory entries is invalid !! It should be equal to 0, by default', 'WARNING')
   
   print_docs("This is, by default, 0 for FAT32 and typically 512 for FAT16.", "17-18", 2, "yes", show_docs = args.verbose)
   print_message("Total number of sectors in the filesystem: {}".format(Fore.GREEN + Style.BRIGHT + str(numOfSectors(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')               # 0  (Always 0 for FAT32)
   
   # Checking the total number of sectors
   if numOfSectors(image) != PREDEFINED_VALUES["SectorsPerFilesystem"] :
      print("\t", end='')
      print_message(f'The total number of sectors is invalid !! It should be equal to 0, by default', 'WARNING')
   print_docs("If the number of sectors is larger than can be represented in this 2-byte value, a 4-byte value exists later in the data structure and this should be 0.", "19-20", 2, "yes", show_docs = args.verbose)
   print_message("Media Descriptor Type: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + str(mediaType(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                               # 0xF8 (Only 2 values are supported (0xF8 and 0xF0)) REFER HERE: https://www.win.tue.nl/~aeb/linux/fs/fat/fat-1.html 
   # Checking the Media type:
   if str(mediaType(image)) not in PREDEFINED_VALUES["MediaType"]: 
      print("\t", end='')
      print_message(f'The media descriptor type is invalid !!', 'WARNING')
   print_docs("According to the Microsoft documentation, 0xf8 should be used for fixed disks and 0xf0 for removable", "21-21", 1, "no", show_docs = args.verbose)
   print_message("Number of sectors Per FAT: {}".format(Fore.GREEN + Style.BRIGHT + str(FATSize(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                                    # 0   (Alyways 0 for FAT32)
   
   # Checking the number of sectors per FAT
   if FATSize(image) != PREDEFINED_VALUES["SectorsPerFat"]:
      print("\t", end='')
      print_message(f'The number of sectors per FAT is invalid !! It should be 0, by default', 'WARNING')
   print_docs("16-bit size in sectors of each FAT for FAT12 and FAT16. For FAT32, this field is 0 by default", "22-23", 2, "yes", show_docs = args.verbose)
   print_message("Number of sectors Per Track: {}".format(Fore.GREEN + Style.BRIGHT + str(numOfSectorsPerTrack(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                     # 63
   print_docs("Sectors per track of storage device.", "24-25", 2, "no", show_docs = args.verbose)
   print_message("Number of Heads: {}".format(Fore.GREEN + Style.BRIGHT + str(numOfHeads(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                                           # 255
   print_docs("Number of heads in storage device.", "26-27", 2, "no", show_docs = args.verbose)
   print_message("Number of Hidden Sectors: {}".format(Fore.GREEN + Style.BRIGHT + str(numOfHiddenSectors(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                          # 8064 (Number of sectors before the start of partition)
   print_docs("Hidden sectors are sectors preceding the start of partition.", "28-31", 4, "no", show_docs = args.verbose)
   print_message("Total number of sectors in the filesystem (Second value): {}".format(Fore.GREEN + Style.BRIGHT + str(totalNumberOfSectors(image)))+ Style.NORMAL + Fore.WHITE, 'INFO') # 15125184 (Either this value or the 16-bit value above must be 0.)
   print_docs("32-bit value of number of sectors in file system. Either this value or the 16-bit value above must be 0.", "32-35", 4, "yes", show_docs = args.verbose)
   print_message("Number of Sectors Per FAT (Second Value): {}".format(Fore.GREEN + Style.BRIGHT + str(numOfHiddenSectors(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')          # 14742
   print_docs("32-bit size in sectors of one File Allocation Table 'FAT'", "36-39", 2, "yes", show_docs = args.verbose)
   print_message("Mirror Flags: " + Fore.GREEN + Style.BRIGHT + str(Flags(image)[:7]) + Fore.RED + str(Flags(image)[7]) + Fore.GREEN + str(Flags(image)[8:]) + Style.NORMAL + Fore.WHITE, 'INFO')                                                   # 0000000000000000 
   print_docs("If " + Fore.RED + "bit 7 " + Fore.YELLOW + "is 1, only one of the FAT structures is active and its index is described in bits 0–3. Otherwise, all FAT structures are mirrors of each other.", "40-41", 4, "yes", show_docs = args.verbose)
   print_message("Filesystem Version: {}".format(Fore.GREEN + Style.BRIGHT + str(FAT32_version(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                                     # 0 (HighByte = Major Version, Low Byte = Minor Version)
   print_docs("The major and minor version number => High Byte = Major Version, Low Byte = Minor Version", "42-43", 2, "yes", show_docs = args.verbose)
   print_message("First cluster of root directory: {}".format(Fore.GREEN + Style.BRIGHT + str(RootDirClusterNumber(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                 # 2 (Usually 2)
   print_docs("Cluster where root directory can be found. Usually 2.", "44-47", 4, "yes", show_docs = args.verbose)
   print_message("Sector Number of Filesystem Information (FSINFO): {}".format(Fore.GREEN + Style.BRIGHT + str(FSINFOSectorNumber(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')  # 1 (Ususally 1)
   print_docs("Sector where FSINFO structure can be found. Usually 1.", "48-49", 2, "no", show_docs = args.verbose)
   print_message("Sector Number of Boot Sector Backup Copy: {}".format(Fore.GREEN + Style.BRIGHT + str(BackupBootSector(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')            # 6 (Ususally 6)
   print_docs("Sector where backup copy of boot sector is located. (Default is 6)", "50-51", 2, "no", show_docs = args.verbose)
   # .... SKIPPING 12 BYTES OF RESERVED AREA ....
   print_docs("RESERVED", "52-63", "no", 12, show_docs = args.verbose)
   print_message("BIOS INT13h drive number: {}".format(Fore.GREEN + Style.BRIGHT + str(BIOSDriveNumber(image)))+ Style.NORMAL + Fore.WHITE, 'INFO')                             # 0 (Usually 0 or 0x80)
   print_docs("Logical Drive Number ofPartition. Usually 0 or 0x80", "64-64", 1, "no", show_docs = args.verbose)
   # .... SKIPPING 1 UNUSED BYTE (used to be Current Head (used by Windows NT) => This line will be printed if in verbose mode
   print_docs("NOT USED. Used to be Current Head (used by Windows NT)", "65-65", 1, "no", show_docs = args.verbose)
   print_message("Extended Boot Signature: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + str(extendedBootSignature(image))) + Style.NORMAL + Fore.WHITE, 'INFO')                # 0x29  (Default: 0x29 =>  Indicates that the three following fields are present.)
   
   # Checking the extended boot signature value:
   if str(extendedBootSignature(image)) != PREDEFINED_VALUES["ExtendedBootSignature"] :
      print("\t", end='')
      print_message(f'The extended boot signature is invalid !! It should be 0x29, by default', 'WARNING')
   print_docs("Extended boot signature to identify if the next three values are valid. Default is 0x29", "66-66", 1, "no", show_docs = args.verbose)
   print_message("Serial Number of the Partition: {}".format(Fore.GREEN + Style.BRIGHT + str(partitionSerialNumber(image))) + Style.NORMAL + Fore.WHITE, 'INFO')                # 2955781185 (Some versions of Windows will calculate this based on the creation date and time.)
   print_docs("Volume serial number, which some versions of Windows will calculate based on the creation date and time.", "67-70", 4, "no", show_docs = args.verbose)
   print_message("Volume name of the Partition: {}".format(Fore.GREEN + Style.BRIGHT + volumeName(image)) + Style.NORMAL + Fore.WHITE, 'INFO')                                  # "NO NAME"
   print_docs("Volume label in ASCII. The user chooses this value when creating the file system.", "71-81", 11, "no", show_docs = args.verbose)
   print_message("Filesystem Type Label: {}".format(Fore.GREEN + Style.BRIGHT + FileSystemType(image)) + Style.NORMAL + Fore.WHITE, 'INFO')                                     # "FAT32"
   
   # Checking the filesystem type label:
   if PREDEFINED_VALUES["FileSystemLabel"] not in FileSystemType(image):
      print("\t", end='')
      print_message(f'The file system label may be invalid !! It should be FAT32 but nothing is required, by default', 'WARNING')
   print_docs("File system type label in ASCII. Standard values include 'FAT32', but nothing is required.", "72-89", 8, "no", show_docs = args.verbose)
   # .... SKIPPING 420 Bytes of Executable Code ....
   print_docs("NOT USED.", "90–509", 420, "no", show_docs = args.verbose)
   print_message("Boot Sector Signature: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + str(BootRecordSignature_1(image)).upper()) + Style.NORMAL + Fore.WHITE, 'INFO')          # 0xAA55 (Default 0xAA55)
   
   # Checking the boot sector signature:
   if BootRecordSignature_1(image) != PREDEFINED_VALUES["BootSectorSignature"] :
      print("\t", end='')
      print_message(f'The boot sector signature is invalid !! It should be 0xAA55, by default', 'ALERT')
   print_docs("Signature value. Default is 0xAA55", "510-511", 2, "no", show_docs = args.verbose)
   FSINFO_StartingSector[partition_number+1] = FSINFOSectorNumber(image)

   #if (args.partition == str(i+1)) :
   #   sys.exit()




def parseFSINFO(args, image, key):
   
   print_message("Parsing" + Fore.MAGENTA + " FSINFO"  + Fore.WHITE + " of Partition {} :".format(Style.BRIGHT + Fore.CYAN + str(key) + Style.NORMAL + Fore.WHITE), 'SUCCESS')  
   print("---------------------------------------\n")
   sleep(1)
   print_message("First FSINFO Signature: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + str(FSINFOSignature_1(image))) + Style.NORMAL + Fore.WHITE, 'INFO')     # 0x41615252 
   
   # Checking the first fsinfo signature value:
   if FSINFOSignature_1(image) != PREDEFINED_VALUES["FSINFO_Signature1"] :
      print("\t", end='')
      print_message(f'The first FSINFO signature may be invalid !! It should be 0x41615252, but nothing is required', 'WARNING')
   print_docs("FSINFO first signature. Default is 0x41615252.", "0-3", 4, "no", show_docs = args.verbose)
   # .... SKIPPING 480 Bytes UNUSED .... #
   print_docs("NOT USED.", "5-483", 480, "no", show_docs = args.verbose)
   print_message("Second FSINFO Signature: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + str(FSINFOSignature_2(image))) + Style.NORMAL + Fore.WHITE, 'INFO')    # 0x61417272 
   
   # Checking the second fsinfo signature value:
   if FSINFOSignature_2(image) != PREDEFINED_VALUES["FSINFO_Signature2"] :
      print("\t", end='')
      print_message(f'The second FSINFO signature may be invalid !! It should be 0x61417272, but nothing is required', 'WARNING')
   print_docs("FSINFO second signature. Default is 0x61417272.", "484-487", 4, "no", show_docs = args.verbose)
   print_message("Number of free clusters: {}".format(Fore.GREEN + Style.BRIGHT + str(NumOfFreeClusters(image))) + Style.NORMAL + Fore.WHITE, 'INFO')           # 1084620
   print_docs("This one is set to 1 if unkown.", "488-491", 4, "no", show_docs = args.verbose)  
   print_message("Sector number of the next free cluster: {}".format(Fore.GREEN + Style.BRIGHT + str(NextFreeClusterSectorNumber(image))) + Style.NORMAL + Fore.WHITE, 'INFO')  # 3
   print_docs("Cluster Number of Cluster that was Most Recently Allocated.", "492-495", 4, "no", show_docs = args.verbose)  
   # .... SKIPPING 12 Bytes RESERVED .... #
   print_docs("NOT USED", "496-507", 12, "no", show_docs = args.verbose)
   print_message("FSINFO Sector Signature: {}".format(Fore.GREEN + Style.BRIGHT + "0x" + str(FsinfoSectorSignature(image)).upper()) + Style.NORMAL + Fore.WHITE, 'INFO')      # 0xAA550000
   
   # Checking the fsinfo sector signature value:
   if FsinfoSectorSignature(image) != PREDEFINED_VALUES["FSINFOSector_Signature"] :
      print("\t", end='')
      print_message(f'The FSINFO sector signature is invalid !! It should be 0xAA550000', 'WARNING')
   print_docs("Signature. Default is 0xAA550000", "508-511", 4, "no", show_docs = args.verbose)







def new_data_block(address, data, args):

  
   if address == 0:
      parseMasterBootRecord(args, data)
   elif address in Partitions_StartingSector:
      parseBootSector(args, data, partition_number = 0)
   elif address in FSINFO_StartingSector:
      parseFSINFO(args, data, key=address)




   



def process_csv_and_feed_blocks(args):
   """
   Reads the CSV file, finds each DATA_BLOCK row,
   gets the address from the previous CMD17 row,
   and calls new_data_block(address, data).
   """
   last_address = None
   # Open the CSV file, replacing NUL characters with nothing to avoid errors
   with open(args.csv, newline='', encoding='utf-8', errors='replace') as csvfile:
      # Read and clean each line to remove NUL characters
      cleaned_lines = (line.replace('\x00', '') for line in csvfile)
      reader = csv.DictReader(cleaned_lines)
      for row in reader:
            #print("Processing row:", row)
            miso_data = row.get('miso_data', '')
            mosi_data = row.get('mosi_data', '')
            # Check for CMD17 and extract address
            cmd17_match = re.match(r'READ_SINGLE_BLOCK \(CMD17\), arg:(\d+)', mosi_data)
            if cmd17_match:
               last_address = int(cmd17_match.group(1))
               print("Found CMD17 with address:", last_address)
            # Check for DATA_BLOCK and use last_address
            elif miso_data and miso_data.startswith('DATA_BLOCK') and last_address is not None:

               data_match = re.match(r'DATA_BLOCK 0x([0-9a-fA-F]+)', miso_data)
               if data_match:
                  data = data_match.group(1).strip()
                  #TO DO : we should not have to pad with zero, find why data is not 512 bytes long
                  #data = data + "0000"
                  if len(data) < 1028:
                     print_message("DATA_BLOCK is only " + str(len(data)/2) + " bytes, padding with zeros", 'WARNING')
                     data = data.zfill(1028)

                  print("Found DATA_BLOCK s:", data)

                  new_data_block(last_address, data, args)
               last_address = None  # Reset after use




def process_image(args):
   # Parsing the Master Boot Record:
   image = raw2hex(args.image, 512)
   parseMasterBootRecord(args, image)


   # Parsing Boot Sector of each FAT32 partition:
   Allowed_Values = ['1', '2', '3', '4'] # Allowed values for the --partition option

   for i in range(len(Partitions_StartingSector)) :
      
      if (args.partition == str(i+1) and Partitions_StartingSector[i] == 0):
         print_message("The selected partition does not have a starting sector.", 'WARNING')
         sys.exit()
      if args.partition :
         if (args.partition not in Allowed_Values) :
            print_message("The partition number you selected does not exist !! Choose a number between 1 and 4 next time.", 'ALERT')
            sys.exit()
         
      if Partitions_StartingSector[i] == 0:
         continue
      elif ((args.partition == str(i+1) and Partitions_StartingSector[i] != 0) or not args.partition):
         image = raw2hex(args.image, 512, Partitions_StartingSector[i]*512)

      parseBootSector(args, image, i)

   if args.partition :
      sys.exit()

   print("\n")

   # Parsing FSINFO of each partition:
   for key in FSINFO_StartingSector:
      image = raw2hex(args.image, 512, Partitions_StartingSector[key-1]*SECTOR_SIZE + BOOT_SECTOR_SIZE + (FSINFO_StartingSector[key] - 1) * SECTOR_SIZE)
      parseFSINFO(args, image, key)






if __name__ == "__main__":
    
    try: 
      parser = argparse.ArgumentParser(description="Master Boot Record and FAT32 file system parser.")
      parser.add_argument("-i", "--image", help="Enter the path to the file system raw image", required=False)
      parser.add_argument("-m", "--mbr", help="Parse Master Boot Record Only", default=False, action="store_true")
      parser.add_argument("-p", "--partition", help="Select the partition number (from 1 to 4) for which you would like to retrieve the boot sector information.", default=False)
      parser.add_argument("-v", "--verbose", help="Be verbose and print out more information", default=False, action="store_true")
      parser.add_argument("-c", "--csv", help="Path to CSV file with SD card data blocks", required=False)
      args = parser.parse_args()

      # If CSV is provided, process it
      if args.csv:
         process_csv_and_feed_blocks(args)
      elif args.image:
         process_image(args)


   


    except KeyboardInterrupt:
         print("\n")
         print(Fore.RED + "[-] ^C The program has been INTERRUPTED !")

    except FileNotFoundError:
         print_message(f"No such file or directory '{args.image}'", 'ALERT') 

    except Exception as e:
        print(Fore.RED + "[-] " + str(e))
        traceback.print_exc()
        print(Fore.WHITE)
