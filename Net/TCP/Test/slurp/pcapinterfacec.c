#ifdef WIN32
#include <winsock2.h>
#include <windows.h>
#endif

#include <mlvalues.h>
#include <alloc.h>
#include <memory.h>
#include <callback.h>
#include <fail.h>
#include <pcap.h>
#include <stdio.h>
#include <string.h>

char errbuf[PCAP_ERRBUF_SIZE];
static value * error_exn = NULL;

void raise_error(char *msg, char *err)
{
  value res;

  if(error_exn == NULL) {
    error_exn = caml_named_value("Pcapinterface.Pcap_error");
    if (error_exn == NULL)
      invalid_argument("Exception Pcapinterface.Pcap_error not initialised.");
  }

  Begin_roots1(res);
  res = alloc_small(3, 0);
  Field(res, 0) = *error_exn;
  Field(res, 1) = copy_string(msg);
  Field(res, 2) = copy_string(err);
  End_roots();
  mlraise(res);
}

CAMLprim value ns_pcap_lookupdev()
{
  char *dev;
  dev = pcap_lookupdev(errbuf);

  if(dev == NULL) {
    raise_error("ns_pcap_lookupdev():", errbuf);
  }

  return copy_string(dev);
}

CAMLprim value ns_pcap_lookupnet(value dev)
{
  bpf_u_int32 netp, maskp;
  value res;

  if(pcap_lookupnet(String_val(dev), &netp, &maskp, errbuf) == -1)
    raise_error("ns_pcap_lookupnet():", errbuf);

  Begin_root(res);
  res = alloc_small(2, 0);
  Field(res, 0) = copy_int64((unsigned int)netp);
  Field(res, 1) = copy_int64((unsigned int)maskp);
  End_roots();
  return res;
}

CAMLprim value ns_pcap_open_live(value dev, value snaplen, value promisc, value to_ms)
{
  value res;
  pcap_t *handle;

  handle = pcap_open_live(String_val(dev), Int_val(snaplen), Bool_val(promisc),
			  Int_val(to_ms), errbuf);

  if(handle == NULL)
    raise_error("ns_pcap_open_live():", errbuf);

  res = Val_long((long)handle);
  return res;
}

CAMLprim value ns_pcap_compile(value handle, value filter, value opt, value netmask)
{
  value res;
  struct bpf_program fp;
  int i=0;

  if(pcap_compile((pcap_t*)Long_val(handle), &fp, String_val(filter),
		  Bool_val(opt), (bpf_u_int32)Int32_val(netmask)) == -1)
     raise_error("ns_pcap_compile():", "Failed");

  res = alloc_string(sizeof(struct bpf_program));
  for(i=0; i<sizeof(struct bpf_program); i++)
    ((char*)res)[i] = ((char*)&fp)[i];

  return res;
}

CAMLprim value ns_pcap_setfilter(value handle, value program)
{
  struct bpf_program fp;
  int i=0;

  for(i=0; i<sizeof(struct bpf_program); i++)
    ((char*)&fp)[i] = ((char *)program)[i];

  if(pcap_setfilter((pcap_t*)Long_val(handle), &fp) == -1)
    raise_error("ns_pcap_getfilter():", pcap_geterr((pcap_t*)handle));

#ifdef WIN32
  ZeroMemory((char*)program, sizeof(struct bpf_program));
#else
  bzero((char*)program, sizeof(struct bpf_program));
#endif

  return Val_unit;
}

CAMLprim value ns_pcap_next(value handle)
{
  value res, record, str, str2, ts;
  unsigned char *pkt;
  struct pcap_pkthdr header;
  int i;

  enter_blocking_section();
  pkt = (unsigned char*)pcap_next((pcap_t*)Long_val(handle), &header);
  leave_blocking_section();

  if(pkt == NULL)
    raise_error("ns_pcap_next():", "returned no data");

  Begin_roots5(res, record, str, str2, ts);
  ts = alloc_small(2, 0);
  Field(ts, 0) = copy_int64(header.ts.tv_sec);
  Field(ts, 1) = copy_int64(header.ts.tv_usec);
  record = alloc_small(3, 0);
  Field(record, 0) = ts;
  Field(record, 1) = copy_int64(header.caplen);
  Field(record, 2) = copy_int64(header.len);

  str2 = Val_int(0);
  for(i=header.caplen-1; i>=0; i--) {
    str = alloc(2, 0);
    Field(str, 0) = Val_int(pkt[i]);
    Field(str, 1) = str2;
    str2 = str;
  }

  res = alloc_small(2, 0);
  Field(res, 0) = record;
  Field(res, 1) = str;
  End_roots();

  return res;
}

CAMLprim value ns_pcap_close(value handle)
{
  pcap_close((pcap_t*)handle);
  return Val_unit;
}



