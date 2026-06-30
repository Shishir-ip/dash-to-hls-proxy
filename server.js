const http = require('http');
const https = require('https');
const crypto = require('crypto');
const url = require('url');

const PORT = process.env.PORT || 3000;
const MPD_URL = 'https://c9851ec-rbm-hilv-fsly.cdn.redbee.live/L26/6b640fa2/a765d074.isml/dash/.mpd';
const CLEAR_KEY_HEX = 'be5383ed3cd8079f4ffe78ad067f476a';
const LIVE_WINDOW_SEGMENTS = 6;

// ========== HTTP UTILS ==========
function fetch(urlStr) {
  return new Promise((resolve, reject) => {
    const client = urlStr.startsWith('https') ? https : http;
    const req = client.get(urlStr, { headers: { 'User-Agent': 'Mozilla/5.0' } }, (res) => {
      const chunks = [];
      res.on('data', chunk => chunks.push(chunk));
      res.on('end', () => resolve(Buffer.concat(chunks)));
    });
    req.on('error', reject);
  });
}

// ========== MPD PARSING ==========
function extractAttrs(tagStr) {
  const attrs = {};
  const regex = /([a-zA-Z_:][a-zA-Z0-9_:\-]*)(?:=["']([^"']*)["'])?/g;
  let m;
  while ((m = regex.exec(tagStr)) !== null) {
    attrs[m[1]] = m[2] !== undefined ? m[2] : '';
  }
  return attrs;
}

function extractTag(xml, tagName) {
  const openRegex = new RegExp(`<(?:[a-zA-Z0-9_]+:)?${tagName}(?:\\s[^>]*)?>`, 'i');
  const openMatch = xml.match(openRegex);
  if (!openMatch) return null;
  const startIdx = openMatch.index;
  const tagStr = openMatch[0];
  if (tagStr.endsWith('/>')) {
    return { tag: tagName, attrs: extractAttrs(tagStr), inner: '', start: startIdx, end: startIdx + tagStr.length };
  }

  const closeRegex = new RegExp(`<\\/(?:[a-zA-Z0-9_]+:)?${tagName}>`, 'gi');
  let depth = 1;
  let searchFrom = startIdx + tagStr.length;
  let endIdx = -1;

  while (depth > 0) {
    const remaining = xml.slice(searchFrom);
    const nextOpen = remaining.match(new RegExp(`<(?:[a-zA-Z0-9_]+:)?${tagName}(?:\\s[^>]*)?>`, 'i'));
    const nextClose = remaining.match(closeRegex);
    const openPos = nextOpen ? searchFrom + nextOpen.index : Infinity;
    const closePos = nextClose ? searchFrom + nextClose.index : Infinity;
    if (closePos === Infinity) break;
    if (openPos < closePos) {
      depth++;
      searchFrom = openPos + nextOpen[0].length;
    } else {
      depth--;
      if (depth === 0) endIdx = closePos + nextClose[0].length;
      searchFrom = closePos + nextClose[0].length;
    }
  }
  if (endIdx === -1) return null;
  const closeTagMatch = xml.slice(startIdx).match(new RegExp(`<\\/(?:[a-zA-Z0-9_]+:)?${tagName}>`, 'i'));
  const actualEnd = closeTagMatch ? startIdx + closeTagMatch.index + closeTagMatch[0].length : endIdx;
  return {
    tag: tagName,
    attrs: extractAttrs(tagStr),
    inner: xml.slice(startIdx + tagStr.length, startIdx + closeTagMatch.index),
    full: xml.slice(startIdx, actualEnd),
    start: startIdx,
    end: actualEnd
  };
}

function extractAllTags(xml, tagName) {
  const results = [];
  let searchXml = xml;
  while (true) {
    const tag = extractTag(searchXml, tagName);
    if (!tag) break;
    results.push(tag);
    searchXml = searchXml.slice(tag.end);
  }
  return results;
}

// ========== MP4 BOX HELPERS ==========
function parseBoxes(buf) {
  const boxes = [];
  let off = 0;
  while (off < buf.length) {
    if (off + 8 > buf.length) break;
    const size = buf.readUInt32BE(off);
    if (size === 0 || size > buf.length - off) break;
    const type = buf.slice(off + 4, off + 8).toString('ascii');
    boxes.push({ type, size, offset: off, data: buf.slice(off, off + size) });
    off += size;
  }
  return boxes;
}

function findBoxDeep(buf, target) {
  const boxes = parseBoxes(buf);
  for (const b of boxes) {
    if (b.type === target) return b.data;
    if (['moof', 'traf', 'moov', 'trak', 'mdia', 'mvex', 'minf', 'stbl', 'stsd', 'sinf', 'schi'].includes(b.type)) {
      const found = findBoxDeep(b.data.slice(8), target);
      if (found) return found;
    }
  }
  return null;
}

function parseTrunSampleSizes(buf) {
  if (buf.length < 16) return [];
  let off = 8;
  const version = buf.readUInt8(off); off += 1;
  const flags = buf.readUIntBE(off, 3); off += 3;
  const sampleCount = buf.readUInt32BE(off); off += 4;
  if (flags & 0x01) off += 4;
  if (flags & 0x04) off += 4;
  const sizes = [];
  for (let i = 0; i < sampleCount; i++) {
    if (off + 4 > buf.length) break;
    if (flags & 0x100) off += 4;
    if (flags & 0x200) {
      sizes.push(buf.readUInt32BE(off));
      off += 4;
    } else {
      off += 4;
    }
    if (flags & 0x400) off += 4;
    if (flags & 0x800) off += 4;
  }
  return sizes;
}

// ========== SAIO/SAIZ ==========
function parseSaio(buf) {
  let off = 8;
  const version = buf.readUInt8(off); off += 1;
  const flags = buf.readUIntBE(off, 3); off += 3;
  if (flags & 0x01) {
    off += 4;
    off += 4;
  }
  const entryCount = buf.readUInt32BE(off); off += 4;
  const offsets = [];
  for (let i = 0; i < entryCount; i++) {
    if (version === 0) {
      offsets.push(buf.readUInt32BE(off));
      off += 4;
    } else {
      offsets.push(Number(buf.readBigUInt64BE(off)));
      off += 8;
    }
  }
  return offsets;
}

function parseSaiz(buf) {
  let off = 8;
  const version = buf.readUInt8(off); off += 1;
  const flags = buf.readUIntBE(off, 3); off += 3;
  if (flags & 0x01) {
    off += 4;
    off += 4;
  }
  const sampleCount = buf.readUInt32BE(off); off += 4;
  const defaultSize = buf.readUInt8(off); off += 1;
  const sizes = [];
  if (defaultSize === 0) {
    for (let i = 0; i < sampleCount; i++) {
      sizes.push(buf.readUInt8(off));
      off += 1;
    }
  } else {
    for (let i = 0; i < sampleCount; i++) {
      sizes.push(defaultSize);
    }
  }
  return { sizes, defaultSize, sampleCount };
}

function parseSencSubsamples(buf) {
  if (buf.length < 16) return { samples: [], hasSubsamples: false };
  let off = 8;
  const version = buf.readUInt8(off); off += 1;
  const flags = buf.readUIntBE(off, 3); off += 3;
  const sampleCount = buf.readUInt32BE(off); off += 4;
  const hasSubsamples = (flags & 0x02) !== 0;
  const samples = [];
  for (let i = 0; i < sampleCount; i++) {
    const sample = {};
    if (hasSubsamples) {
      if (off + 2 > buf.length) break;
      const subCount = buf.readUInt16BE(off); off += 2;
      sample.subsamples = [];
      for (let j = 0; j < subCount; j++) {
        if (off + 6 > buf.length) break;
        const clear = buf.readUInt16BE(off); off += 2;
        const enc = buf.readUInt32BE(off); off += 4;
        sample.subsamples.push({ clearBytes: clear, encryptedBytes: enc });
      }
    }
    samples.push(sample);
  }
  return { samples, hasSubsamples };
}

// ========== DECRYPTION ==========
function padIV(iv8) {
  const padded = Buffer.alloc(16);
  iv8.copy(padded);
  return padded;
}

function advanceCounter8(iv8, blocks) {
  const res = Buffer.from(iv8);
  let carry = blocks;
  for (let i = 7; i >= 0; i--) {
    const sum = res[i] + carry;
    res[i] = sum & 0xFF;
    carry = sum >>> 8;
    if (carry === 0) break;
  }
  return padIV(res);
}

function decryptCENC(data, keyHex) {
  const key = Buffer.from(keyHex, 'hex');
  const boxes = parseBoxes(data);
  let moof = null, mdat = null;
  for (const b of boxes) {
    if (b.type === 'moof') moof = b;
    if (b.type === 'mdat') mdat = b;
  }
  if (!moof || !mdat) return data;

  const sencBox = findBoxDeep(moof.data, 'senc');
  if (!sencBox) return data;
  const sencInfo = parseSencSubsamples(sencBox);
  if (sencInfo.samples.length === 0) return data;

  const saioBox = findBoxDeep(moof.data, 'saio');
  const saizBox = findBoxDeep(moof.data, 'saiz');
  const ivSize = 8;
  let samples = [];

  if (saioBox && saizBox) {
    const saio = parseSaio(saioBox);
    const saiz = parseSaiz(saizBox);
    const moofStart = moof.offset;
    for (let i = 0; i < saiz.sampleCount; i++) {
      const auxOffset = moofStart + saio[0] + (i > 0 ? saiz.sizes.slice(0, i).reduce((a, b) => a + b, 0) : 0);
      const auxSize = saiz.sizes[i];
      if (auxOffset + auxSize > data.length) {
        samples.push({ iv: Buffer.alloc(ivSize), subsamples: sencInfo.samples[i]?.subsamples });
        continue;
      }
      const auxData = data.slice(auxOffset, auxOffset + auxSize);
      let off = 0;
      const iv = auxData.slice(off, off + ivSize);
      off += ivSize;
      const sample = { iv, subsamples: sencInfo.samples[i]?.subsamples };
      if (auxSize > ivSize) {
        const subCount = auxData.readUInt16BE(off);
        off += 2;
        sample.subsamples = [];
        for (let j = 0; j < subCount; j++) {
          const clear = auxData.readUInt16BE(off);
          off += 2;
          const enc = auxData.readUInt32BE(off);
          off += 4;
          sample.subsamples.push({ clearBytes: clear, encryptedBytes: enc });
        }
      }
      samples.push(sample);
    }
  } else {
    for (let i = 0; i < sencInfo.samples.length; i++) {
      samples.push({ iv: Buffer.alloc(ivSize), subsamples: sencInfo.samples[i]?.subsamples });
    }
  }

  if (samples.length === 0) return data;
  const trunData = findBoxDeep(moof.data, 'trun');
  const sampleSizes = trunData ? parseTrunSampleSizes(trunData) : [];

  const mdatOffset = mdat.offset + 8;
  const mdatSize = mdat.size - 8;
  const payload = data.slice(mdatOffset, mdatOffset + mdatSize);
  const decrypted = Buffer.from(payload);

  let byteOffset = 0;
  for (let i = 0; i < samples.length; i++) {
    const sample = samples[i];
    const size = sampleSizes[i] || Math.floor(mdatSize / samples.length);

    if (sample.subsamples && sample.subsamples.length > 0) {
      let pos = 0;
      let blockCounter = 0;
      for (const sub of sample.subsamples) {
        pos += sub.clearBytes;
        if (sub.encryptedBytes > 0) {
          const chunk = decrypted.slice(byteOffset + pos, byteOffset + pos + sub.encryptedBytes);
          const iv = advanceCounter8(sample.iv, blockCounter);
          const cipher = crypto.createDecipheriv('aes-128-ctr', key, iv);
          const plain = Buffer.concat([cipher.update(chunk), cipher.final()]);
          plain.copy(decrypted, byteOffset + pos);
          pos += sub.encryptedBytes;
          blockCounter += Math.ceil(sub.encryptedBytes / 16);
        }
      }
    } else {
      const chunk = decrypted.slice(byteOffset, byteOffset + size);
      const iv = advanceCounter8(sample.iv, 0);
      const cipher = crypto.createDecipheriv('aes-128-ctr', key, iv);
      const plain = Buffer.concat([cipher.update(chunk), cipher.final()]);
      plain.copy(decrypted, byteOffset);
    }
    byteOffset += size;
  }

  const output = Buffer.alloc(data.length);
  data.copy(output);
  decrypted.copy(output, mdatOffset);
  return output;
}

// ========== URL HELPERS ==========
function getBaseUrl(mpdXml, mpdUrl) {
  const ismlMatch = mpdUrl.match(/(.*\.isml\/)/);
  if (ismlMatch) {
    const base = ismlMatch[1];
    const baseMatch = mpdXml.match(/<(?:[a-zA-Z0-9_]+:)?BaseURL(?:\s[^>]*)?>([^<]*)<\/(?:[a-zA-Z0-9_]+:)?BaseURL>/i);
    if (baseMatch) {
      const txt = baseMatch[1].trim();
      return base + (txt.endsWith('/') ? txt : txt + '/');
    }
    return base;
  }
  return mpdUrl.substring(0, mpdUrl.lastIndexOf('/') + 1);
}

function parseTimeline(timelineXml, timescale, n) {
  const entries = extractAllTags(timelineXml, 'S');
  const entryInfos = [];
  let totalSegs = 0, currentTime = 0;
  for (const entry of entries) {
    const t = entry.attrs.t !== undefined ? parseInt(entry.attrs.t) : currentTime;
    const d = parseInt(entry.attrs.d);
    const r = entry.attrs.r !== undefined ? parseInt(entry.attrs.r) : 0;
    const count = r + 1;
    entryInfos.push({ t, d, count, startIndex: totalSegs });
    totalSegs += count;
    currentTime = t + count * d;
  }
  const startIndex = Math.max(0, totalSegs - n);
  const segments = [];
  let maxDuration = 0;
  for (const info of entryInfos) {
    const endIndex = info.startIndex + info.count;
    if (endIndex <= startIndex) continue;
    const segStartInEntry = Math.max(0, startIndex - info.startIndex);
    for (let i = segStartInEntry; i < info.count; i++) {
      const duration = info.d / timescale;
      segments.push({ time: info.t + i * info.d, duration });
      if (duration > maxDuration) maxDuration = duration;
    }
  }
  return { segments, maxDuration };
}

// ========== SERVER ==========
let cachedMPD = null, cachedMPDTime = 0;

async function getMPD() {
  if (cachedMPD && Date.now() - cachedMPDTime < 2000) return cachedMPD;
  cachedMPD = (await fetch(MPD_URL)).toString();
  cachedMPDTime = Date.now();
  return cachedMPD;
}

const server = http.createServer(async (req, res) => {
  const parsedUrl = url.parse(req.url, true);
  const path = parsedUrl.pathname;
  const cors = {
    'Access-Control-Allow-Origin': '*',
    'Access-Control-Allow-Methods': 'GET, HEAD, OPTIONS',
    'Access-Control-Allow-Headers': '*'
  };

  if (req.method === 'OPTIONS') {
    res.writeHead(204, cors);
    res.end();
    return;
  }

  try {
    const host = req.headers.host || 'localhost';

    if (path === '/live.m3u8' || path === '/master.m3u8') {
      const mpdXml = await getMPD();
      const mpd = extractTag(mpdXml, 'MPD');
      const period = extractTag(mpd.inner, 'Period');
      const adaptationSets = extractAllTags(period.inner, 'AdaptationSet');

      const videoReps = [], audioReps = [];
      for (const as of adaptationSets) {
        const mime = as.attrs.mimeType || as.attrs.contentType || '';
        const isVideo = mime.includes('video') || as.attrs.contentType === 'video';
        const isAudio = mime.includes('audio') || as.attrs.contentType === 'audio';
        const representations = extractAllTags(as.inner, 'Representation');
        for (const rep of representations) {
          const item = {
            id: rep.attrs.id,
            bandwidth: rep.attrs.bandwidth,
            codecs: rep.attrs.codecs || '',
            width: rep.attrs.width,
            height: rep.attrs.height,
            type: isVideo ? 'video' : isAudio ? 'audio' : 'unknown'
          };
          if (isVideo) videoReps.push(item);
          else if (isAudio) audioReps.push(item);
        }
      }
      videoReps.sort((a, b) => parseInt(b.bandwidth) - parseInt(a.bandwidth));

      let m3u8 = '#EXTM3U\n#EXT-X-VERSION:6\n';
      if (audioReps.length) {
        const audio = audioReps[0];
        m3u8 += `#EXT-X-MEDIA:TYPE=AUDIO,GROUP-ID="audio",NAME="Audio",DEFAULT=YES,AUTOSELECT=YES,URI="https://${host}/media/audio/${encodeURIComponent(audio.id)}.m3u8"\n`;
      }
      for (const v of videoReps) {
        m3u8 += `#EXT-X-STREAM-INF:BANDWIDTH=${v.bandwidth},CODECS="${v.codecs}"`;
        if (v.width && v.height) m3u8 += `,RESOLUTION=${v.width}x${v.height}`;
        if (audioReps.length) m3u8 += `,AUDIO="audio"`;
        m3u8 += `\nhttps://${host}/media/video/${encodeURIComponent(v.id)}.m3u8\n`;
      }

      res.writeHead(200, { ...cors, 'Content-Type': 'application/vnd.apple.mpegurl', 'Cache-Control': 'max-age=2' });
      res.end(m3u8);
      return;
    }

    if (path.startsWith('/media/')) {
      const match = path.match(/\/media\/(video|audio)\/(.+)\.m3u8/);
      if (!match) {
        res.writeHead(400, cors);
        res.end('Bad path');
        return;
      }
      const [, , repId] = match;

      const mpdXml = await getMPD();
      const mpd = extractTag(mpdXml, 'MPD');
      const period = extractTag(mpd.inner, 'Period');

      let targetRep = null, targetAs = null;
      const adaptationSets = extractAllTags(period.inner, 'AdaptationSet');
      for (const as of adaptationSets) {
        const reps = extractAllTags(as.inner, 'Representation');
        for (const rep of reps) {
          if (rep.attrs.id === repId) {
            targetRep = rep;
            targetAs = as;
            break;
          }
        }
        if (targetRep) break;
      }

      if (!targetRep) {
        res.writeHead(404, cors);
        res.end('Rep not found');
        return;
      }

      let segTemplate = extractTag(targetRep.inner, 'SegmentTemplate');
      if (!segTemplate) segTemplate = extractTag(targetAs.inner, 'SegmentTemplate');
      if (!segTemplate) {
        res.writeHead(500, cors);
        res.end('No SegmentTemplate');
        return;
      }

      const stAttrs = segTemplate.attrs;
      const initTemplate = stAttrs.initialization;
      const mediaTemplate = stAttrs.media;
      const timescale = parseInt(stAttrs.timescale || '1');

      const baseUrl = getBaseUrl(mpdXml, MPD_URL);
      const initUrl = baseUrl + initTemplate.replace(/\$RepresentationID\$/g, repId);

      const segmentTimeline = extractTag(segTemplate.inner, 'SegmentTimeline');
      if (!segmentTimeline) {
        res.writeHead(500, cors);
        res.end('No SegmentTimeline');
        return;
      }

      const result = parseTimeline(segmentTimeline.inner, timescale, LIVE_WINDOW_SEGMENTS);
      const segments = result.segments;
      const maxDuration = result.maxDuration;

      if (segments.length === 0) {
        res.writeHead(500, cors);
        res.end('No segments');
        return;
      }

      const targetDuration = Math.ceil(maxDuration);
      let m3u8 = '#EXTM3U\n#EXT-X-VERSION:6\n';
      m3u8 += `#EXT-X-TARGETDURATION:${targetDuration}\n`;
      m3u8 += `#EXT-X-MEDIA-SEQUENCE:0\n`;
      m3u8 += `#EXT-X-MAP:URI="https://${host}/init?url=${encodeURIComponent(initUrl)}"\n`;

      for (const seg of segments) {
        const segUrl = baseUrl + mediaTemplate
          .replace(/\$RepresentationID\$/g, repId)
          .replace(/\$Time\$/g, seg.time)
          .replace(/\$Number\$/g, '0')
          .replace(/\$Bandwidth\$/g, '0');
        const proxyUrl = `https://${host}/segment?url=${encodeURIComponent(segUrl)}`;
        m3u8 += `#EXTINF:${seg.duration.toFixed(3)},\n${proxyUrl}\n`;
      }

      res.writeHead(200, { ...cors, 'Content-Type': 'application/vnd.apple.mpegurl', 'Cache-Control': 'max-age=2' });
      res.end(m3u8);
      return;
    }

    if (path.startsWith('/init')) {
      const initUrl = parsedUrl.query.url;
      if (!initUrl) {
        res.writeHead(400, cors);
        res.end('Missing url');
        return;
      }
      const data = await fetch(initUrl);
      res.writeHead(200, { ...cors, 'Content-Type': 'video/mp4', 'Cache-Control': 'max-age=3600' });
      res.end(data);
      return;
    }

    if (path.startsWith('/segment')) {
      const segUrl = parsedUrl.query.url;
      if (!segUrl) {
        res.writeHead(400, cors);
        res.end('Missing url');
        return;
      }
      const data = await fetch(segUrl);
      const clear = decryptCENC(data, CLEAR_KEY_HEX);
      res.writeHead(200, { ...cors, 'Content-Type': 'video/mp4', 'Cache-Control': 'max-age=2' });
      res.end(clear);
      return;
    }

    // ========== DEBUG ENDPOINT ==========
    if (path === '/debug-segment') {
      const segUrl = parsedUrl.query.url || 'https://c9851ec-rbm-hilv-fsly.cdn.redbee.live/L26/6b640fa2/a765d074.isml/dash/a765d074-video=3500000-1069699069536.dash';
      
      try {
        const data = await fetch(segUrl);
        const boxes = parseBoxes(data);
        const moof = boxes.find(b => b.type === 'moof');
        const mdat = boxes.find(b => b.type === 'mdat');
        
        let sencFound = false, sencSize = 0, saioFound = false, saizFound = false;
        if (moof) {
          const sencBox = findBoxDeep(moof.data, 'senc');
          if (sencBox) { sencFound = true; sencSize = sencBox.length; }
          saioFound = !!findBoxDeep(moof.data, 'saio');
          saizFound = !!findBoxDeep(moof.data, 'saiz');
        }
        
        let decryptResult = 'Not attempted';
        let nalCheck = 'no mdat';
        try {
          const clear = decryptCENC(data, CLEAR_KEY_HEX);
          const clearBoxes = parseBoxes(clear);
          const clearMdat = clearBoxes.find(b => b.type === 'mdat');
          if (clearMdat) {
            const first4 = clearMdat.data.readUInt32BE(8);
            if (first4 === 0x00000001 || (first4 >>> 8) === 0x000001) {
              nalCheck = 'NAL start code found ✓';
            } else {
              nalCheck = `No NAL start code. First 4 bytes: 0x${first4.toString(16).padStart(8, '0')}`;
            }
          }
          decryptResult = `Success ${clear.length} bytes`;
        } catch (e) {
          decryptResult = `Failed: ${e.message}`;
        }
        
        const report = `
Segment URL: ${segUrl}
Total size: ${data.length} bytes
Top-level boxes: ${boxes.map(b => b.type).join(', ')}
moof found: ${!!moof}
senc found: ${sencFound} (size: ${sencSize} bytes)
saio found: ${saioFound}
saiz found: ${saizFound}

Decryption: ${decryptResult}
NAL check: ${nalCheck}
`;
        res.writeHead(200, { ...cors, 'Content-Type': 'text/plain' });
        res.end(report);
      } catch (err) {
        res.writeHead(500, { ...cors, 'Content-Type': 'text/plain' });
        res.end(`Error: ${err.message}`);
      }
      return;
    }

    res.writeHead(404, cors);
    res.end('Not Found');
  } catch (err) {
    res.writeHead(500, { ...cors, 'Content-Type': 'text/plain' });
    res.end(`Error: ${err.message}\n${err.stack}`);
  }
});

server.listen(PORT, () => {
  console.log(`DASH-to-HLS proxy running on port ${PORT}`);
});
