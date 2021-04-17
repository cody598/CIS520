#include "userprog/process.h"
#include <debug.h>
#include <inttypes.h>
#include <round.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "userprog/gdt.h"
#include "userprog/pagedir.h"
#include "userprog/tss.h"
#include "filesys/directory.h"
#include "filesys/file.h"
#include "filesys/filesys.h"
#include "threads/flags.h"
#include "threads/init.h"
#include "threads/interrupt.h"
#include "threads/malloc.h"
#include "threads/palloc.h"
#include "threads/thread.h"
#include "threads/vaddr.h"
#include "devices/timer.h"
#include "userprog/syscall.h"
#include "vm/frame.h"

struct memoryMappedFile
{
  mapid_t mapid;
  struct file* file;
  void * start_addr;
  unsigned pg_cnt; 
  struct hash_elem elem;
};


static thread_func start_process NO_RETURN;
static bool load (const char *cmdline, void (**eip) (void), void **esp);


/* Functionalities required by memory mapped files hash table */
/* Returns a hash value. */
unsigned mmfile_hash (const struct hash_elem *, void *);
/* Returns true if mmfile a's mapid is less than b's */
bool mmfile_less (const struct hash_elem *, const struct hash_elem *, void *);

/* Functionalities for memory mapped files table*/
/* free the memory mapped files table */
void free_mmfiles (struct hash *);
/* Helper function for free_mmfiles, used to free resources for each entry
   represented by a hash_elem */
static void free_mmfiles_entry (struct hash_elem *, void *);
/* The real release of the the resources is done in this function, which 
   includes all the pages in supplemental page table */
static void mmfiles_free_entry (struct memoryMappedFile* mmf_ptr);
/* Allocate a new unique mapid */
static mapid_t alloc_mapid (void);

/* Starts a new thread running a user program loaded from
   filename.  The new thread may be scheduled (and may even exit)
   before process_execute() returns.  Returns the new process's
   thread id, or TID_ERROR if the thread cannot be created. */
tid_t
process_execute (const char *file_name) 
{
  char *fn_copy;
  tid_t tid;
  struct child_status *child; 
  struct thread *currentThread;

  /* Make a copy of the filename.*/
  fn_copy = palloc_get_page (0);
  if (fn_copy == NULL)
    return TID_ERROR;
  strlcpy (fn_copy, file_name, PGSIZE);
  
  char *cmd_name, *args;
  cmd_name = strtok_r (fn_copy, " ", &args);

  /* Create a new thread in order to execute the given filename. */
  tid = thread_create (cmd_name, PRI_DEFAULT, start_process, args);
  if (tid == TID_ERROR)
  {
	  palloc_free_page (fn_copy);
  }
    
  else 
  { 
    currentThread = thread_current ();
    child = calloc (1, sizeof *child);
    if (child != NULL) 
    {
		child->id = tid;
		child->exit_called = false;
		child->has_waited = false;
		list_push_back(&currentThread->children, &child->elem_status);
    }
  }  
  return tid;
}

/* A thread function that loads a user process and starts it
   running. */
static void
start_process (void *file_name_)
{
  char *file_name = file_name_;
  struct intr_frame if_;
  bool success;
  int load_status;
  struct thread *currentThread = thread_current ();
  struct thread *parentThread;

   /* init supplemental hash page table */
  hash_init (&currentThread->suppl_page_table, suppl_pt_hash, suppl_pt_less, NULL);

  /* init memory mapped files table */
  hash_init (&currentThread->mmfiles, mmfile_hash, mmfile_less, NULL);
  
  /* Initialize interrupt frame and load executable. */
  memset (&if_, 0, sizeof if_);
  if_.gs = if_.fs = if_.es = if_.ds = if_.ss = SEL_UDSEG;
  if_.cs = SEL_UCSEG;
  if_.eflags = FLAG_IF | FLAG_MBS;
  success = load (file_name, &if_.eip, &if_.esp);

  /* If load failed, get out. */
  if (!success)
    load_status = -1;
  else
    load_status = 1;

  currentThread = thread_current (); 
  parentThread = thread_get_by_id (currentThread->parent_id);
  if (parentThread != NULL)
    {
      lock_acquire(&parentThread->lock_child);
      parentThread->child_load_status = load_status;
      cond_signal(&parentThread->cond_child, &parentThread->lock_child);
      lock_release(&parentThread->lock_child);
    }

  if (!success)
    thread_exit ();
  palloc_free_page (pg_round_down(file_name));
  
  /* Start the user process by simulating a return from an
     interrupt, implemented by intr_exit (in
     threads/intr-stubs.S).  Because intr_exit takes all of its
     arguments on the stack in the form of a `struct intr_frame',
     we just point the stack pointer (%esp) to our stack frame
     and jump to it. */
  asm volatile ("movl %0, %%esp; jmp intr_exit" : : "g" (&if_) : "memory");
  NOT_REACHED ();
}

/* Waits for thread TID to die and returns its exit status.  If
   it was terminated by the kernel (i.e. killed due to an
   exception), returns -1.  If TID is invalid or if it was not a
   child of the calling process, or if process_wait() has already
   been successfully called for the given TID, returns -1
   immediately, without waiting.

   This function will be implemented in problem 2-2.  For now, it
   does nothing. */
int
process_wait (tid_t child_tid) 
{
  int tidStatus;
  struct thread *currentThread;
  struct child_status *childStatus = NULL;
  struct list_elem *elem;
  if (child_tid != TID_ERROR)
   {
     currentThread = thread_current ();
     elem = list_tail (&currentThread->children);
     while ((elem = list_prev (elem)) != list_head (&currentThread->children))
       {
         childStatus = list_entry(elem, struct child_status, elem_status);
         if (childStatus->id == child_tid)
           break;
       }

     if (childStatus == NULL)
       tidStatus = -1;
     else
       {
         lock_acquire(&currentThread->lock_child);
         while (thread_get_by_id (child_tid) != NULL)
           cond_wait (&currentThread->cond_child, &currentThread->lock_child);
         if (!childStatus->exit_called || childStatus->has_waited)
           tidStatus = -1;
         else
           { 
             tidStatus = childStatus->exit_status;
             childStatus->has_waited = true;
           }
         lock_release(&currentThread->lock_child);
       }
   }
  else 
    tidStatus = TID_ERROR;
  return tidStatus;
}

/* Free the current process's resources. */
void
process_exit (void)
{
  struct thread *currentThread = thread_current ();
  uint32_t *pd;
  struct thread *parentThread;
  struct list_elem *elem;
  struct list_elem *next;
  struct child_status *childStatus;

  /* unmap all memory-mapped files*/
  free_mmfiles (&currentThread->mmfiles);
  
  /* Destroy the current process's page directory and switch back
     to the kernel-only page directory. */
  pd = currentThread->pagedir;
  if (pd != NULL) 
    {
	  /* Set current threads page directory to null so it can't switch to process page directory. */
      currentThread->pagedir = NULL;
      pagedir_activate (NULL);
      pagedir_destroy (pd);
    }
 /*free up the children list*/
  elem = list_begin (&currentThread->children);
  while (elem != list_tail(&currentThread->children))
    {
      next = list_next (elem);
      childStatus = list_entry (elem, struct child_status, elem_status);
      list_remove (elem);
      free (childStatus);
      elem = next;
    }

  /*Enable the file's write property */
  if (currentThread->exec_file != NULL)
    file_allow_write (currentThread->exec_file);

  /*If current thread owns files, those files are freed. */
  close_file_by_owner (currentThread->tid); 

  /* Free supplemental page table */
  free_suppl_pt (&currentThread->suppl_page_table);  

  parentThread = thread_get_by_id (currentThread->parent_id);
  if (parentThread != NULL)
    {
      lock_acquire (&parentThread->lock_child);
      if (parentThread->child_load_status == 0)
	    parentThread->child_load_status = -1;
      cond_signal (&parentThread->cond_child, &parentThread->lock_child);
      lock_release (&parentThread->lock_child);
    }
}

/* Sets up the CPU for running user code in the current
   thread.
   This function is called on every context switch. */
void
process_activate (void)
{
  struct thread *t = thread_current ();

  /* Activate thread's page tables. */
  pagedir_activate (t->pagedir);

  /* Set thread's kernel stack for use in processing
     interrupts. */
  tss_update ();
}

/* We load ELF binaries.  The following definitions are taken
   from the ELF specification, [ELF1], more-or-less verbatim.  */

/* ELF types.  See [ELF1] 1-2. */
typedef uint32_t Elf32_Word, Elf32_Addr, Elf32_Off;
typedef uint16_t Elf32_Half;

/* For use with ELF types in printf(). */
#define PE32Wx PRIx32   /* Print Elf32_Word in hexadecimal. */
#define PE32Ax PRIx32   /* Print Elf32_Addr in hexadecimal. */
#define PE32Ox PRIx32   /* Print Elf32_Off in hexadecimal. */
#define PE32Hx PRIx16   /* Print Elf32_Half in hexadecimal. */

/* Executable header.  See [ELF1] 1-4 to 1-8.
   This appears at the very beginning of an ELF binary. */
struct Elf32_Ehdr
  {
    unsigned char e_ident[16];
    Elf32_Half    e_type;
    Elf32_Half    e_machine;
    Elf32_Word    e_version;
    Elf32_Addr    e_entry;
    Elf32_Off     e_phoff;
    Elf32_Off     e_shoff;
    Elf32_Word    e_flags;
    Elf32_Half    e_ehsize;
    Elf32_Half    e_phentsize;
    Elf32_Half    e_phnum;
    Elf32_Half    e_shentsize;
    Elf32_Half    e_shnum;
    Elf32_Half    e_shstrndx;
  };

/* Program header.  See [ELF1] 2-2 to 2-4.
   There are e_phnum of these, starting at file offset e_phoff
   (see [ELF1] 1-6). */
struct Elf32_Phdr
  {
    Elf32_Word p_type;
    Elf32_Off  p_offset;
    Elf32_Addr p_vaddr;
    Elf32_Addr p_paddr;
    Elf32_Word p_filesz;
    Elf32_Word p_memsz;
    Elf32_Word p_flags;
    Elf32_Word p_align;
  };

/* Values for p_type.  See [ELF1] 2-3. */
#define PT_NULL    0            /* Ignore. */
#define PT_LOAD    1            /* Loadable segment. */
#define PT_DYNAMIC 2            /* Dynamic linking info. */
#define PT_INTERP  3            /* Name of dynamic loader. */
#define PT_NOTE    4            /* Auxiliary info. */
#define PT_SHLIB   5            /* Reserved. */
#define PT_PHDR    6            /* Program header table. */
#define PT_STACK   0x6474e551   /* Stack segment. */

/* Flags for p_flags.  See [ELF3] 2-3 and 2-4. */
#define PF_X 1          /* Executable. */
#define PF_W 2          /* Writable. */
#define PF_R 4          /* Readable. */

static bool setup_stack (void **esp, const char *file_name);
static bool validate_segment (const struct Elf32_Phdr *, struct file *);
static bool load_segment (struct file *file, off_t ofs, uint8_t *upage,
                          uint32_t read_bytes, uint32_t zero_bytes,
                          bool writable);
						  
static bool load_segment_lazily (struct file *file, off_t ofs, uint8_t *upage,
                          uint32_t read_bytes, uint32_t zero_bytes,
                          bool writable);					

/* Loads an ELF executable from FILE_NAME into the current thread.
   Stores the executable's entry point into *EIP
   and its initial stack pointer into *ESP.
   Returns true if successful, false otherwise. */
bool
load (const char *file_name, void (**eip) (void), void **esp) 
{
  struct thread *t = thread_current ();
  struct Elf32_Ehdr ehdr;
  struct file *file = NULL;
  off_t file_ofs;
  bool success = false;
  int i;

  /* Allocate and activate page directory. */
  t->pagedir = pagedir_create ();
  if (t->pagedir == NULL) 
    goto done;
  process_activate ();

  /* Open executable file. Thread name is the actual file name as its parsed out.*/
  file = filesys_open (t->name);
  if (file == NULL) 
    {
      printf ("load: %s: open failed\n", t->name);
	  file_close (file);
	  goto done; 
    }
  t->exec_file = file; 
  file_deny_write (file);
  
  /* Read and verify executable header. */
  if (file_read (file, &ehdr, sizeof ehdr) != sizeof ehdr
      || memcmp (ehdr.e_ident, "\177ELF\1\1\1", 7)
      || ehdr.e_type != 2
      || ehdr.e_machine != 3
      || ehdr.e_version != 1
      || ehdr.e_phentsize != sizeof (struct Elf32_Phdr)
      || ehdr.e_phnum > 1024) 
    {
      printf ("load: %s: error loading executable\n", file_name);
      goto done; 
    }

  /* Read program headers. */
  file_ofs = ehdr.e_phoff;
  for (i = 0; i < ehdr.e_phnum; i++) 
    {
      struct Elf32_Phdr phdr;

      if (file_ofs < 0 || file_ofs > file_length (file))
        goto done;
      file_seek (file, file_ofs);

      if (file_read (file, &phdr, sizeof phdr) != sizeof phdr)
        goto done;
      file_ofs += sizeof phdr;
      switch (phdr.p_type) 
        {
        case PT_NULL:
        case PT_NOTE:
        case PT_PHDR:
        case PT_STACK:
        default:
          /* Ignore this segment. */
          break;
        case PT_DYNAMIC:
        case PT_INTERP:
        case PT_SHLIB:
          goto done;
        case PT_LOAD:
          if (validate_segment (&phdr, file)) 
            {
              bool writable = (phdr.p_flags & PF_W) != 0;
              uint32_t file_page = phdr.p_offset & ~PGMASK;
              uint32_t mem_page = phdr.p_vaddr & ~PGMASK;
              uint32_t page_offset = phdr.p_vaddr & PGMASK;
              uint32_t read_bytes, zero_bytes;
              if (phdr.p_filesz > 0)
                {
                  /* Normal segment.
                     Read initial part from disk and zero the rest. */
                  read_bytes = page_offset + phdr.p_filesz;
                  zero_bytes = (ROUND_UP (page_offset + phdr.p_memsz, PGSIZE)
                                - read_bytes);
                }
              else 
                {
                  /* Entirely zero.
                     Don't read anything from disk. */
                  read_bytes = 0;
                  zero_bytes = ROUND_UP (page_offset + phdr.p_memsz, PGSIZE);
                }
              if (!load_segment_lazily(file, file_page, (void *) mem_page,
                                 read_bytes, zero_bytes, writable))
                goto done;
            }
          else
            goto done;
          break;
        }
    }

  /* Set up stack. */
  if (!setup_stack (esp, file_name))
    goto done;

  /* Start address. */
  *eip = (void (*) (void)) ehdr.e_entry;

  success = true;

 done:
  /* We arrive here whether the load is successful or not. */
  return success;
}

/* load() helpers. */

static bool install_page (void *upage, void *kpage, bool writable);

/* Checks whether PHDR describes a valid, loadable segment in
   FILE and returns true if so, false otherwise. */
static bool
validate_segment (const struct Elf32_Phdr *phdr, struct file *file) 
{
  /* p_offset and p_vaddr must have the same page offset. */
  if ((phdr->p_offset & PGMASK) != (phdr->p_vaddr & PGMASK)) 
    return false; 

  /* p_offset must point within FILE. */
  if (phdr->p_offset > (Elf32_Off) file_length (file)) 
    return false;

  /* p_memsz must be at least as big as p_filesz. */
  if (phdr->p_memsz < phdr->p_filesz) 
    return false; 

  /* The segment must not be empty. */
  if (phdr->p_memsz == 0)
    return false;
  
  /* The virtual memory region must both start and end within the
     user address space range. */
  if (!is_user_vaddr ((void *) phdr->p_vaddr))
    return false;
  if (!is_user_vaddr ((void *) (phdr->p_vaddr + phdr->p_memsz)))
    return false;

  /* The region cannot "wrap around" across the kernel virtual
     address space. */
  if (phdr->p_vaddr + phdr->p_memsz < phdr->p_vaddr)
    return false;

  /* Disallow mapping page 0.
     Not only is it a bad idea to map page 0, but if we allowed
     it then user code that passed a null pointer to system calls
     could quite likely panic the kernel by way of null pointer
     assertions in memcpy(), etc. */
  if (phdr->p_vaddr < PGSIZE)
    return false;

  /* It's okay. */
  return true;
}

/* Loads a segment starting at offset OFS in FILE at address
   UPAGE lazily */
static bool
load_segment_lazily (struct file *file, off_t ofs, uint8_t *upage,
		     uint32_t read_bytes, uint32_t zero_bytes, bool writable) 
{
  ASSERT ((read_bytes + zero_bytes) % PGSIZE == 0);
  ASSERT (pg_ofs (upage) == 0);
  ASSERT (ofs % PGSIZE == 0);

  while (read_bytes > 0 || zero_bytes > 0) 
    {
      /* Calculate how to fill this page.
         We will read PAGE_READ_BYTES bytes from FILE
         and zero the final PAGE_ZERO_BYTES bytes. */
      size_t page_read_bytes = read_bytes < PGSIZE ? read_bytes : PGSIZE;
      size_t page_zero_bytes = PGSIZE - page_read_bytes;

      /* Add an file suuplemental page entry to supplemental page table */ 
      if (!suppl_pt_insert_file (file, ofs, upage, page_read_bytes,
                                 page_zero_bytes, writable))
	return false;

      /* Advance. */
      read_bytes -= page_read_bytes;
      zero_bytes -= page_zero_bytes;
      ofs += page_read_bytes;
      upage += PGSIZE;
    }
  return true;

}

/* Loads a segment starting at offset OFS in FILE at address
   UPAGE.  In total, READ_BYTES + ZERO_BYTES bytes of virtual
   memory are initialized, as follows:

        - READ_BYTES bytes at UPAGE must be read from FILE
          starting at offset OFS.

        - ZERO_BYTES bytes at UPAGE + READ_BYTES must be zeroed.

   The pages initialized by this function must be writable by the
   user process if WRITABLE is true, read-only otherwise.

   Return true if successful, false if a memory allocation error
   or disk read error occurs. */
static bool
load_segment (struct file *file, off_t ofs, uint8_t *upage,
              uint32_t read_bytes, uint32_t zero_bytes, bool writable) 
{
  ASSERT ((read_bytes + zero_bytes) % PGSIZE == 0);
  ASSERT (pg_ofs (upage) == 0);
  ASSERT (ofs % PGSIZE == 0);

  file_seek (file, ofs);
  while (read_bytes > 0 || zero_bytes > 0) 
    {
      /* Calculate how to fill this page.
         We will read PAGE_READ_BYTES bytes from FILE
         and zero the final PAGE_ZERO_BYTES bytes. */
      size_t page_read_bytes = read_bytes < PGSIZE ? read_bytes : PGSIZE;
      size_t page_zero_bytes = PGSIZE - page_read_bytes;

      /* Get a page of memory. */
      uint8_t *kpage = vm_allocate_frame (PAL_USER);
      if (kpage == NULL)
        return false;

      /* Load this page. */
      if (file_read (file, kpage, page_read_bytes) != (int) page_read_bytes)
        {
          vm_free_frame (kpage);
          return false; 
        }
      memset (kpage + page_read_bytes, 0, page_zero_bytes);

      /* Add the page to the process's address space. */
      if (!install_page (upage, kpage, writable)) 
        {
          vm_free_frame (kpage);
          return false; 
        }

      /* Advance. */
      read_bytes -= page_read_bytes;
      zero_bytes -= page_zero_bytes;
      upage += PGSIZE;
    }
  return true;
}

/* Create a minimal stack by mapping a zeroed page at the top of
   user virtual memory. */
static bool
setup_stack (void **esp, const char *file_name) 
{
  uint8_t *kpage;
  bool success = false;

  kpage = vm_allocate_frame (PAL_USER | PAL_ZERO);
    if (kpage != NULL)
	{
	  success = install_page (((uint8_t *) PHYS_BASE) - PGSIZE, kpage, true);
	  if (success) 
	  {
		*esp = PHYS_BASE-24;

		uint8_t *argstr_head;
		char *cmd_name = thread_current ()->name;
		int string_length, total_length;
		int argc;

		/*Add the arguments "string" into stack*/
		string_length = strlen(file_name) + 1;
		*esp -= string_length;
		memcpy(*esp, file_name, string_length);
		total_length += string_length;

		/*push command name into stack*/
		string_length = strlen(cmd_name) + 1;
		*esp -= string_length;
		argstr_head = *esp;
		memcpy(*esp, cmd_name, string_length);
		total_length += string_length;

		/*set alignment, get the starting address, modify *esp */
		*esp -= 4 - total_length % 4;

		/* push argv[argc] null into the stack */
		*esp -= 4;
		* (uint32_t *) *esp = (uint32_t) NULL;

		/* Iterates through the file name using both the current_address and total_length as bounds. */
		 
		int i = total_length - 1;
		/*Omits ' ' and '\0' */
		while (*(argstr_head + i) == ' ' ||  *(argstr_head + i) == '\0')
		  {
			if (*(argstr_head + i) == ' ')
			  {
				*(argstr_head + i) = '\0';
			  }
			i--;
		  }

		/*Iterates through args string, then pushes args address onto stack*/
		char *arg;
		for (arg = (char *)(argstr_head + i); i > 0;
			 i--, arg = (char*)(argstr_head+i))
		  {
			/* Searches for args, and if found it pushes its address to stack */
			if ( (*arg == '\0' || *arg == ' ') &&
				 (*(arg+1) != '\0' && *(arg+1) != ' '))
			  {
				*esp -= 4;
				* (uint32_t *) *esp = (uint32_t) arg + 1;
				argc++;
			  }
			/*set space to '\0', so that each arg string will terminate*/
			if (*arg == ' ')
			  *arg = '\0';
		  }

		/* Push an additional arg, the command line, into the stack*/
		*esp -= 4;
		* (uint32_t *) *esp = (uint32_t) argstr_head;
		argc++;

		/*Push argv*/
		* (uint32_t *) (*esp - 4) = *(uint32_t *) esp;
		*esp -= 4;

		/*Pusg argc*/
		*esp -= 4;
		* (int *) *esp = argc;

		/*Push the final return address*/
		*esp -= 4;
		* (uint32_t *) *esp = 0x0;
	  } 
	  else
	  {
		vm_free_frame (kpage);
	  }
	}
    return success;
}

/* Maps the page to the virtual address if NULL. Additionally the page will be writeable based upon the writeable parameter */
static bool
install_page (void *upage, void *kpage, bool writable)
{
  struct thread *t = thread_current ();

  /* Check and make sure that the page location is empty, then map the page to that virtual address. */
  return (pagedir_get_page (t->pagedir, upage) == NULL
          && pagedir_set_page (t->pagedir, upage, kpage, writable));
}

/* Returns a hash value. */
unsigned
mmfile_hash (const struct hash_elem *p_, void *aux UNUSED)
{
  const struct memoryMappedFile *p = hash_entry (p_, struct memoryMappedFile, elem);
  return hash_bytes (&p->mapid, sizeof p->mapid);
}

/* Returns true if mmfile a's mapid less than b's */
bool
mmfile_less (const struct hash_elem *a_, const struct hash_elem *b_,
           void *aux UNUSED)
{
  const struct memoryMappedFile *a = hash_entry (a_, struct memoryMappedFile, elem);
  const struct memoryMappedFile *b = hash_entry (b_, struct memoryMappedFile, elem);

  return a->mapid < b->mapid;
}

/* Add an entry in memory mapped files table, and add entries in
   supplemental page table iteratively which is in mmfiles_insert's
   semantic. */
mapid_t mmfiles_insert (void *addr, struct file* file, int32_t len)
{
  struct thread *t = thread_current ();
  struct memoryMappedFile *mmf;
  struct hash_elem *result;
  int offset;
  int pg_cnt;

  mmf = calloc (1, sizeof *mmf);
  if (mmf == NULL)
    return -1;

  mmf->mapid = alloc_mapid ();
  mmf->file = file;
  mmf->start_addr = addr;

  /* count how many pages we need to contain the file, and insert a 
     corresponding entry for each file page */
  offset = 0;
  pg_cnt = 0;
  while (len > 0)
    {
      size_t read_bytes = len < PGSIZE ? len : PGSIZE; 
      if (!suppl_pt_insert_mmf (file, offset, addr, read_bytes))
	return -1;

      offset += PGSIZE;
      len -= PGSIZE;
      addr += PGSIZE;
      pg_cnt++;
    }

  mmf->pg_cnt = pg_cnt;  

  result = hash_insert (&t->mmfiles, &mmf->elem);
  if (result != NULL)
    return -1;

  return mmf->mapid;
}

/* Remove the entry in memory mapped files table, and remove corresponding
   entries in supplemental page table iteratively which is in 
   mmfiles_remove()'s semantic. */
void
mmfiles_remove (mapid_t mapping)
{
  struct thread *t = thread_current ();
  struct memoryMappedFile mmf;
  struct memoryMappedFile *mmf_ptr;
  struct hash_elem *he;

  mmf.mapid = mapping;
  he = hash_delete (&t->mmfiles, &mmf.elem);
  if (he != NULL)
    {
      mmf_ptr = hash_entry (he, struct memoryMappedFile, elem);
      mmfiles_free_entry (mmf_ptr);
    }
}

static void
mmfiles_free_entry (struct memoryMappedFile* mmf_ptr)
{
  struct thread *t = thread_current ();
  struct hash_elem *he;
  int pg_cnt;
  struct suppl_pte spte;
  struct suppl_pte *spte_ptr;
  int offset;

  pg_cnt = mmf_ptr->pg_cnt;
  offset = 0;
  while (pg_cnt-- > 0)
    {
      /* Get supplemental page table entry for each page */
      /* check whether the page is dirty */
      /* if dirty, write back to the file*/
      /* free the struct suppl_pte for each entry*/
      spte.uvaddr = mmf_ptr->start_addr + offset;
      he = hash_delete (&t->suppl_page_table, &spte.elem);
      if (he != NULL)
	{
	  spte_ptr = hash_entry (he, struct suppl_pte, elem);
	  if (spte_ptr->is_loaded
	      && pagedir_is_dirty (t->pagedir, spte_ptr->uvaddr))
	    {
	      /* write back to disk */
	      lock_acquire (&fs_lock);
	      file_seek (spte_ptr->data.mmf_page.file, 
			 spte_ptr->data.mmf_page.ofs);
	      file_write (spte_ptr->data.mmf_page.file, 
			  spte_ptr->uvaddr,
			  spte_ptr->data.mmf_page.read_bytes);
	      lock_release (&fs_lock);
	    }
	  free (spte_ptr);
	}
      offset += PGSIZE;
    }

  lock_acquire (&fs_lock);
  file_close (mmf_ptr->file);
  lock_release (&fs_lock);

  free (mmf_ptr);
}


/* allocate a new unique mapid */
static mapid_t
alloc_mapid ()
{
  return thread_current ()->mapid_allocator++;
}

/* free the memory mapped files table */
void 
free_mmfiles (struct hash *mmfiles)
{
  hash_destroy (mmfiles, free_mmfiles_entry);
}

/* Helper function for free_mmfiles, used to free resources for each entry
   represented by a hash_elem */
static void
free_mmfiles_entry (struct hash_elem *e, void *aux UNUSED)
{
  struct memoryMappedFile *mmf;
  mmf = hash_entry (e, struct memoryMappedFile, elem);
  mmfiles_free_entry (mmf);
}