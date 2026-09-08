"""Only upload receipts and source mappings are durable; Prove2Me owns the math."""
import json
import os
from pathlib import Path
from urllib.parse import urlparse


def empty_state():
    return {"version": 1, "items": {}, "completed": {}, "deferred": {}}


class Storage:
    def __init__(self, location):
        self.location = location
        self.client = None
        if location.startswith("s3://"):
            import boto3
            parsed = urlparse(location)
            self.bucket, self.prefix = parsed.netloc, parsed.path.strip("/")
            if not self.prefix.startswith("prove2me/"):
                raise ValueError("Use an existing R2 bucket with a prove2me/ prefix")
            self.client = boto3.client("s3", endpoint_url=os.environ["R2_ENDPOINT_URL"], region_name="auto")
        else:
            self.directory = Path(location)
            self.directory.mkdir(parents=True, exist_ok=True)

    def read(self, name, default=None):
        if name not in {"state.json", "catalog.json"}:
            raise ValueError("Unsupported checkpoint object")
        if self.client:
            try:
                data = self.client.get_object(Bucket=self.bucket, Key=f"{self.prefix}/{name}")["Body"].read()
            except self.client.exceptions.NoSuchKey:
                return default
        else:
            file = self.directory / name
            if not file.exists():
                return default
            data = file.read_bytes()
        return json.loads(data)

    def write(self, name, value):
        if name not in {"state.json", "catalog.json"}:
            raise ValueError("Unsupported checkpoint object")
        data = (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()
        if self.client:
            self.client.put_object(Bucket=self.bucket, Key=f"{self.prefix}/{name}", Body=data, ContentType="application/json")
        else:
            file = self.directory / name
            temporary = file.with_suffix(".tmp")
            with temporary.open("wb") as output:
                output.write(data)
                output.flush()
                os.fsync(output.fileno())
            temporary.replace(file)
